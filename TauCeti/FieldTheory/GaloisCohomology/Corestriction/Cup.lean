/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.TrivialF2

/-!
# Corestriction and cup products across a finite field extension

For a finite extension `L/K` embedded in a separable closure of `K`, restriction and
corestriction on continuous cohomology with trivial `𝔽₂` coefficients satisfy the projection
formula

```text
cor (res x ⌣ y) = x ⌣ cor y.
```

The formula computes the corestriction of a degree-two cup product in which one factor is the
restriction of a degree-one class on `G_K`: that ambient class can be pulled outside the
corestriction, so only the degree-one corestriction of the other factor remains to be computed.

## Main result

* `TauCeti.galoisCor_cup`: the degree-`(1,1)` projection formula.

## Reference

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (1.5.3)(iv).
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u

variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K) [FiniteDimensional K L]

/-- **The degree-`(1,1)` projection formula for a finite field extension**:
`cor (res x ⌣ y) = x ⌣ cor y` on continuous cohomology with trivial `𝔽₂` coefficients
(NSW (1.5.3)(iv)). -/
theorem galoisCor_cup
    (x : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup K)))
    (y : continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup L))) :
    galoisCor K L σ 2
        ((trivialF2TopPairing (AbsoluteGaloisGroup L)).cup 1 1
          (galoisRes K L σ 1 x) y) =
      (trivialF2TopPairing (AbsoluteGaloisGroup K)).cup 1 1 x
        (galoisCor K L σ 1 y) := by
  let U := (galoisSubgroup K L σ).toSubgroup
  have htransport :
      (galoisF2Iso K L σ 2).inv
          ((trivialF2TopPairing (AbsoluteGaloisGroup L)).cup 1 1
            ((galoisF2Iso K L σ 1).hom
              (trivialF2ResMap (AbsoluteGaloisGroup K) U 1 x)) y) =
        (trivialF2TopPairing U).cup 1 1
          (trivialF2ResMap (AbsoluteGaloisGroup K) U 1 x)
          ((galoisF2Iso K L σ 1).inv y) := by
    have h := trivialF2Map_cup
      (ContinuousMonoidHom.toContinuousMonoidHom (galoisSubgroupEquiv K L σ).symm)
      1 1 ((galoisF2Iso K L σ 1).hom
        (trivialF2ResMap (AbsoluteGaloisGroup K) U 1 x)) y
    rw [← galoisF2Iso_inv K L σ, ← galoisF2Iso_inv K L σ,
      Iso.hom_inv_id_apply] at h
    simpa using h
  simp only [galoisCor_def, galoisRes_def, ConcreteCategory.comp_apply]
  rw [htransport]
  exact trivialF2CorMap_cup_one_one (AbsoluteGaloisGroup K) U
    (galoisSubgroup K L σ).isOpen x ((galoisF2Iso K L σ 1).inv y)

end TauCeti
