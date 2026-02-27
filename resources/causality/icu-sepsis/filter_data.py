import pandas as pd
import numpy as np
from sklearn.ensemble import RandomForestClassifier

# 1. Load your feature data
df = pd.read_csv('values_raw.csv')
X = df

# 2. Load your target actions (labels)
# Note: You must export your labels to a file first, 
# or run this directly inside your MDP generation script.
# For demonstration, we assume a CSV with your target actions:
y = pd.read_csv('labels.csv')['action'] 

# 3. Train a Random Forest
# Forests evaluate how well features split the data, 
# which directly translates to your Z3 decision tree.
rf = RandomForestClassifier(n_estimators=100, random_state=42)
rf.fit(X, y)

# 4. Extract and rank feature importances
importances = pd.Series(rf.feature_importances_, index=X.columns)
importances_sorted = importances.sort_values(ascending=False)

print("Top 10 Most Important Features:")
print(importances_sorted.head(10))

# 5. Select the top K features (e.g., K = 8)
K = 8
top_k_features = importances_sorted.head(K).index.tolist()

# 6. Save the reduced dataset
df_filtered = df[top_k_features]
df_filtered.to_csv('values.csv', index=False)
print(f"\nSaved {K} selected features to 'values.csv'")
