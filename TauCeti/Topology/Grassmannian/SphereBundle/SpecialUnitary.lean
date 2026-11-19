/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.StiefelFibration.SpecialUnitary

/-!
# The sphere bundle `SU(n) → SU(1 + n) → S^(2n+1)`

For `𝕜 = ℝ` or `ℂ` (any `RCLike 𝕜`), evaluating a special unitary matrix on the first coordinate
vector `e₀` gives the map `SU(1 + n) → S`, `A ↦ A e₀` (`TauCeti.specialUnitarySphereMap`), to the
unit sphere `S` of `EuclideanSpace 𝕜 (Fin (1 + n))`. Over `ℂ` this sphere is `S^(2n+1)`. The
fibre of the map over `e₀` is the block subgroup `diag(1, SU(n))`, the image of
`Matrix.specialUnitaryGroup.fromBlocksOne 𝕜 1 n`. For `n ≥ 1` the map is surjective and a locally
trivial bundle with fibre `SU(n)`, and hence a Serre fibration. For `n = 2` and `𝕜 = ℂ` this is the
bundle `SU(2) → SU(3) → S⁵`, with the block inclusion `B ↦ diag(1, B)` and the projection to the
first column.

A unit vector is an orthonormal one-frame (`TauCeti.finiteOrthonormalFrame.sphereHomeomorph`), and
under this identification `A ↦ A e₀` is the special unitary Stiefel map
`TauCeti.specialUnitaryFrameMap 1 n`. So every statement is read off from
`TauCeti.Topology.Grassmannian.StiefelFibration.SpecialUnitary`, whose charts transfer to the
sphere along the homeomorphism (`Bundle.Trivialization.homeomorphComp`). For `n = 0` the map is not
surjective: `SU(1)` is trivial, while the unit sphere of `𝕜` is not a point.

## Main definitions

* `TauCeti.specialUnitarySphereMap`: the evaluation map `SU(1 + n) → S`, `A ↦ A e₀`.

## Main results

* `TauCeti.specialUnitarySphereMap_eq_specialUnitarySphereMap_one_iff`: the fibre over `e₀` is the
  image of `SU(n)`.
* `TauCeti.exists_trivialization_specialUnitarySphereMap`: a chart with fibre `SU(n)` around each
  point of the sphere.
* `TauCeti.specialUnitarySphereMap_mem_serreFibrations`: `SU(1 + n) → S` is a Serre fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (the fibre bundles
  `SU(n) → SU(n + 1) → S^(2n+1)`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open Matrix Metric Set Topology

noncomputable section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### The evaluation map `SU(1 + n) → S^(2n+1)` -/

variable (n : ℕ)

/-- The evaluation map `SU(1 + n) → S`, `A ↦ A e₀`, on the first coordinate vector `e₀`, to the
unit sphere `S` of `EuclideanSpace 𝕜 (Fin (1 + n))`. -/
def specialUnitarySphereMap (A : specialUnitaryGroup (Fin (1 + n)) 𝕜) :
    sphere (0 : EuclideanSpace 𝕜 (Fin (1 + n))) 1 :=
  finiteOrthonormalFrame.sphereHomeomorph 𝕜 (1 + n) (specialUnitaryFrameMap 1 n A)

variable {n}

/-- In coordinates, `specialUnitarySphereMap n A` is the first column `A e₀` of `A`. -/
@[simp]
theorem coe_specialUnitarySphereMap (A : specialUnitaryGroup (Fin (1 + n)) 𝕜) :
    (specialUnitarySphereMap n A : EuclideanSpace 𝕜 (Fin (1 + n))) =
      WithLp.toLp 2 ((A : Matrix (Fin (1 + n)) (Fin (1 + n)) 𝕜).col 0) := by
  -- `Fin.castAdd n (0 : Fin 1)` is not syntactically `0 : Fin (1 + n)`, and `Fin.castLE_zero`
  -- needs the target written as `Fin (m + 1)`, so the cast of `0` is normalized by hand.
  simp [specialUnitarySphereMap, show Fin.castAdd n (0 : Fin 1) = 0 from Fin.ext (by simp)]

variable (𝕜 n) in
/-- The evaluation map `SU(1 + n) → S` is continuous. -/
theorem continuous_specialUnitarySphereMap :
    Continuous (specialUnitarySphereMap (𝕜 := 𝕜) n) :=
  (finiteOrthonormalFrame.sphereHomeomorph 𝕜 (1 + n)).continuous.comp
    (continuous_specialUnitaryFrameMap 𝕜 1 n)

/-- The fibre of `A ↦ A e₀` over `e₀` is the block subgroup `diag(1, SU(n))`. -/
theorem specialUnitarySphereMap_eq_specialUnitarySphereMap_one_iff
    {A : specialUnitaryGroup (Fin (1 + n)) 𝕜} :
    specialUnitarySphereMap n A = specialUnitarySphereMap n 1 ↔
      A ∈ (specialUnitaryGroup.fromBlocksOne 𝕜 1 n).range := by
  rw [specialUnitarySphereMap, specialUnitarySphereMap,
    (finiteOrthonormalFrame.sphereHomeomorph 𝕜 (1 + n)).injective.eq_iff,
    specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff]

/-- For `n ≥ 1`, every unit vector of `𝕜^(1 + n)` is `A e₀` for some `A ∈ SU(1 + n)`. -/
theorem surjective_specialUnitarySphereMap [NeZero n] :
    Function.Surjective (specialUnitarySphereMap (𝕜 := 𝕜) n) :=
  (finiteOrthonormalFrame.sphereHomeomorph 𝕜 (1 + n)).surjective.comp
    surjective_specialUnitaryFrameMap

/-! ### Local triviality -/

/-- For `n ≥ 1`, the evaluation map `SU(1 + n) → S` has a chart with fibre `SU(n)` around each
point of the sphere. -/
theorem exists_trivialization_specialUnitarySphereMap [NeZero n]
    (b : sphere (0 : EuclideanSpace 𝕜 (Fin (1 + n))) 1) :
    ∃ e : Bundle.Trivialization (specialUnitaryGroup (Fin n) 𝕜) (specialUnitarySphereMap n),
      b ∈ e.baseSet := by
  obtain ⟨e, he⟩ := exists_trivialization_specialUnitaryFrameMap
    ((finiteOrthonormalFrame.sphereHomeomorph 𝕜 (1 + n)).symm b)
  exact ⟨e.homeomorphComp (finiteOrthonormalFrame.sphereHomeomorph 𝕜 (1 + n)), he⟩

/-- For `n ≥ 1`, the evaluation map `SU(1 + n) → S`, `A ↦ A e₀`, is a Serre fibration: it is
locally trivial with fibre `SU(n)`. For `n = 2` and `𝕜 = ℂ` this is `SU(2) → SU(3) → S⁵`. -/
theorem specialUnitarySphereMap_mem_serreFibrations [NeZero n] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialUnitarySphereMap n, continuous_specialUnitarySphereMap 𝕜 n⟩ :
        _root_.TopCat.of (specialUnitaryGroup (Fin (1 + n)) 𝕜) ⟶
          _root_.TopCat.of (sphere (0 : EuclideanSpace 𝕜 (Fin (1 + n))) 1)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := specialUnitaryGroup (Fin n) 𝕜) exists_trivialization_specialUnitarySphereMap

end TauCeti
