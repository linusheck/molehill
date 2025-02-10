"""Get a bandit."""
from bayesianbandits import (
    Arm,
    NormalInverseGammaRegressor,
    Agent,
    ThompsonSampling,
    UpperConfidenceBound,
)

def get_bandit():
    arms = [
        Arm(1, learner=NormalInverseGammaRegressor()),
        Arm(2, learner=NormalInverseGammaRegressor())
    ]

    policy = UpperConfidenceBound(alpha=0.1)

    return Agent(arms, ThompsonSampling())
