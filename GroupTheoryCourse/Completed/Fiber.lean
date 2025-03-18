import GroupTheoryCourse.Completed.Homomorphism

variable {G H} [Group G] [Group H]

def fiber (φ : G →* H) (y : H) :=
  { x : G | φ x = y }

def ker (φ : G →* H) := fiber φ 1
