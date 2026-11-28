/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere.Isotopy
public import TauCeti.Geometry.Diffeomorphism.AddCircle
public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Circle
public import Mathlib.Topology.Homotopy.Equiv
import TauCeti.Geometry.Diffeomorphism.Composition
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.AddCircle
import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Path
import TauCeti.Topology.Homotopy.DeformationRetract

/-!
# The diffeomorphism group of the circle

Every `C^m` diffeomorphism of the circle `S¹ ⊆ ℝ²`, `m ≠ 0`, is joined in the weak Whitney
topology to the restriction of an orthogonal transformation of `ℝ²`, namely to the identity or to
the reflection `(x, y) ↦ (x, -y)`. So the map `π₀ O(2) → π₀ Diff(S¹)` induced by the reference
inclusion `TauCeti.orthogonalToDiffSphere` is surjective; it is injective by
`TauCeti.joined_orthogonalToDiffSphere_iff`, and `Diff(S¹)` has exactly two path components. This
is the one-dimensional case of the isotopy classification of sphere diffeomorphisms whose
three-dimensional case is Cerf's theorem `TauCeti.CerfTheorem`.

More is true for `0 < m ≤ ∞`: the reference inclusion `O(2) → Diff(S¹)` is a homotopy
equivalence, the one-dimensional case of the statement whose three-dimensional case is the Smale
conjecture `TauCeti.SmaleConjecture`. In fact `Diff(S¹)` deformation retracts onto `O(2)`
(`TauCeti.diffCircleStraighteningHomotopy`). Read through `AddCircle.diffeomorphSphere`, the
straightening homotopy `AddCircle.straighteningHomotopy` deforms `Diff(ℝ / ℤ)` onto the isometries
`θ ↦ a ± θ`, and these are exactly the diffeomorphisms that `AddCircle.diffeomorphSphere` carries to
restrictions of orthogonal transformations: through `θ ↦ exp (2πiθ)` they are the restrictions of
the real linear isometries `z ↦ u z` and `z ↦ u * conj z` of `ℂ`
(`AddCircle.mem_isometryDiffeomorphs_iff_exists_linearIsometryEquiv`). Since `O(2)` is compact,
its image in `Diff(S¹)` is homeomorphic to it (`TauCeti.isClosedEmbedding_orthogonalToDiffSphere`),
which makes the retraction `TauCeti.diffCircleToOrthogonal` continuous.

The isotopy straightens a lift of the diffeomorphism to the identity lift. Read through the
parametrization `AddCircle.diffeomorphSphere` of `S¹` by `ℝ / ℤ`, `θ ↦ (cos 2πθ, sin 2πθ)`, a
diffeomorphism or its composite with the reflection `θ ↦ -θ` has a lift `F : ℝ → ℝ` with
`F (x + 1) = F x + 1` and `F' > 0`, and the convex combinations of `F` with the identity lift a
diffeotopy from the identity to it (`Diffeomorph.exists_diffeotopy_final_eq_or_final_eq_comp_neg`).
The reflection `θ ↦ -θ` of `ℝ / ℤ` is the reflection `(x, y) ↦ (x, -y)` of `S¹`.

## Main results

* `TauCeti.exists_joined_orthogonalToDiffSphere_circle`: every diffeomorphism of `S¹` is isotopic
  to an orthogonal transformation.
* `TauCeti.natCard_zerothHomotopy_diff_circle`: `Diff(S¹)` has two path components.
* `TauCeti.diffCircleToOrthogonal`: the straightening retraction `Diff(S¹) → O(2)`, a left inverse
  of the reference inclusion (`TauCeti.diffCircleToOrthogonal_orthogonalToDiffSphere`).
* `TauCeti.diffCircleStraighteningHomotopy`: `Diff(S¹)` deformation retracts onto `O(2)`.
* `TauCeti.orthogonalToDiffCircleHomotopyEquiv`: the reference inclusion `O(2) → Diff(S¹)` is a
  homotopy equivalence.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Princeton University Press (2012),
  Section 2.1, for lifts of circle homeomorphisms and the two isotopy classes of homeomorphisms of
  the circle.
-/

public section

open Metric
open scoped Manifold ContDiff TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {m : ℕ∞ω}

/-- **Diffeomorphisms of the circle are isotopic to orthogonal ones.** Every `C^m` diffeomorphism
of the circle `S¹ ⊆ ℝ²`, `m ≠ 0`, is joined in the weak Whitney topology to the restriction of an
orthogonal transformation of `ℝ²`. -/
theorem exists_joined_orthogonalToDiffSphere_circle (hm : m ≠ 0)
    (f : Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) m) :
    ∃ A : Matrix.orthogonalGroup (Fin 2) ℝ, Joined (orthogonalToDiffSphere 1 m A) f := by
  set ψ := AddCircle.diffeomorphSphere 1 m
  obtain ⟨Ψ, hΨ⟩ :=
    Diffeomorph.exists_diffeotopy_final_eq_or_final_eq_comp_neg (Diffeomorph.diffCongr ψ.symm f) hm
  -- Conjugating the diffeotopy back to `S¹` joins the identity to `ψ ∘ Ψ.final ∘ ψ⁻¹`.
  have hJ : Joined 1 (Diffeomorph.diffCongr ψ Ψ.final) := by
    simpa using Ψ.joined_one_final.map (Diffeomorph.continuous_diffCongr ψ)
  rcases hΨ with hΨ | hΨ
  · -- The diffeotopy ends at the conjugate of `f`, so `f` is joined to the identity.
    refine ⟨1, ?_⟩
    rw [map_one]
    simpa only [DFunLike.coe_injective hΨ, ← Diffeomorph.diffCongr_symm,
      MulEquiv.apply_symm_apply] using hJ
  · -- The diffeotopy ends at the conjugate of `f * ρ`, for the reflection `ρ`, which `ψ` reads as
    -- `θ ↦ -θ`. So `f * ρ` is joined to the identity and `f` to `ρ⁻¹`.
    set ρ := orthogonalToDiffSphere 1 m (orthogonalDiagonalReflection ℝ 1)
    have hfρ : Ψ.final = (Diffeomorph.diffCongr ψ).symm (f * ρ) := by
      rw [map_mul, Diffeomorph.diffCongr_symm]
      refine Diffeomorph.ext fun θ ↦ ?_
      rw [hΨ, Function.comp_apply, Diffeomorph.mul_apply,
        Diffeomorph.diffCongr_apply_apply ψ.symm ρ]
      -- `ψ.symm.symm` is `ψ` by definition, so `diffeomorphSphere_neg` applies.
      exact congrArg _ (ψ.toEquiv.eq_symm_apply.2 (AddCircle.diffeomorphSphere_neg 1 m θ))
    refine ⟨(orthogonalDiagonalReflection ℝ 1)⁻¹, ?_⟩
    rw [hfρ, MulEquiv.apply_symm_apply] at hJ
    rw [map_inv]
    simpa only [mul_inv_cancel_right, one_mul] using hJ.map (continuous_mul_const ρ⁻¹)

/-- **The diffeomorphism group of the circle has two path components**, for the weak Whitney
`C^m` topology, `m ≠ 0`: those of the identity and of a reflection. -/
theorem natCard_zerothHomotopy_diff_circle (hm : m ≠ 0) :
    Nat.card (ZerothHomotopy (Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) m)) = 2 :=
  forall_exists_joined_orthogonalToDiffSphere_iff_natCard_zerothHomotopy_eq_two.1
    (exists_joined_orthogonalToDiffSphere_circle hm)

/-! ### The homotopy equivalence `O(2) ≃ Diff(S¹)` -/

section HomotopyEquiv

variable {n : ℕ∞}

/-- Conjugating a diffeomorphism `g` of `ℝ / ℤ` to `S¹` through `AddCircle.diffeomorphSphere`
gives the restriction of an orthogonal transformation exactly when `g` is one of the isometries
`θ ↦ a ± θ`. -/
private theorem diffCongr_mem_range_orthogonalToDiffSphere_iff
    (g : AddCircle (1 : ℝ) ≃ₘ^n⟮𝓘(ℝ), 𝓘(ℝ)⟯ AddCircle (1 : ℝ)) :
    Diffeomorph.diffCongr (AddCircle.diffeomorphSphere 1 n) g ∈
        Set.range (orthogonalToDiffSphere 1 n) ↔
      g ∈ AddCircle.isometryDiffeomorphs 1 n := by
  set ψ := AddCircle.diffeomorphSphere (1 : ℝ) n
  set b := Complex.orthonormalBasisOneI.repr
  have hψ (θ : AddCircle (1 : ℝ)) : (ψ θ : EuclideanSpace ℝ (Fin 2)) = b θ.toCircle :=
    AddCircle.coe_diffeomorphSphere_apply 1 n θ
  rw [AddCircle.mem_isometryDiffeomorphs_iff_exists_linearIsometryEquiv]
  constructor
  · -- An orthogonal `A` gives the linear isometry `b⁻¹ ∘ A ∘ b` of `ℂ`.
    rintro ⟨A, hA⟩
    refine ⟨b.trans ((Matrix.UnitaryGroup.toLinearIsometryEquiv A).trans b.symm), fun θ ↦ ?_⟩
    have h := congrArg (fun φ ↦ (φ (ψ θ) : EuclideanSpace ℝ (Fin 2))) hA
    simp only [coe_orthogonalToDiffSphere_apply, Diffeomorph.diffCongr_apply_apply,
      Diffeomorph.symm_apply_apply, hψ] at h
    simp [h]
  · -- A linear isometry `L` of `ℂ` gives the orthogonal matrix of `b ∘ L ∘ b⁻¹`.
    rintro ⟨L, hL⟩
    refine ⟨Matrix.UnitaryGroup.ofLinearIsometryEquiv (b.symm.trans (L.trans b)),
      Diffeomorph.ext fun x ↦ Subtype.ext ?_⟩
    obtain ⟨θ, rfl⟩ := ψ.surjective x
    simp [hψ, hL]

/-- The straightening of `Diff(AddCircle 1)`, transported to `Diff(S¹)` by conjugation. -/
private noncomputable def straightenSphere (hn : n ≠ 0) (t : unitInterval)
    (f : Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) :
    Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n :=
  Diffeomorph.diffCongr (AddCircle.diffeomorphSphere 1 n)
    (AddCircle.straightenDiffeomorph hn t
      (Diffeomorph.diffCongr (AddCircle.diffeomorphSphere 1 n).symm f))

private theorem continuous_straightenSphere (hn : n ≠ 0) :
    Continuous fun p : unitInterval × Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n ↦
      straightenSphere hn p.1 p.2 :=
  (Diffeomorph.continuous_diffCongr _).comp <| (AddCircle.continuous_straightenDiffeomorph hn).comp
    (continuous_fst.prodMk ((Diffeomorph.continuous_diffCongr _).comp continuous_snd))

private theorem straightenSphere_zero (hn : n ≠ 0)
    (f : Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) :
    straightenSphere hn 0 f = f := by
  rw [straightenSphere, AddCircle.straightenDiffeomorph_zero, ← Diffeomorph.diffCongr_symm,
    MulEquiv.apply_symm_apply]

/-- At time `1` the straightening lands on the orthogonal transformations. -/
private theorem straightenSphere_one_mem_range (hn : n ≠ 0)
    (f : Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) :
    straightenSphere hn 1 f ∈ Set.range (orthogonalToDiffSphere 1 n) := by
  have h := (AddCircle.straighteningRetraction hn
    (Diffeomorph.diffCongr (AddCircle.diffeomorphSphere 1 n).symm f)).property
  rw [AddCircle.coe_straighteningRetraction_apply] at h
  exact (diffCongr_mem_range_orthogonalToDiffSphere_iff _).2 h

/-- The straightening fixes the orthogonal transformations at all times. -/
private theorem straightenSphere_of_mem_range (hn : n ≠ 0) (t : unitInterval)
    {f : Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n}
    (hf : f ∈ Set.range (orthogonalToDiffSphere 1 n)) : straightenSphere hn t f = f := by
  rw [← MulEquiv.apply_symm_apply (Diffeomorph.diffCongr (AddCircle.diffeomorphSphere 1 n)) f,
    Diffeomorph.diffCongr_symm] at hf
  obtain ⟨_, _, _, hg⟩ := AddCircle.mem_isometryDiffeomorphs.1
    ((diffCongr_mem_range_orthogonalToDiffSphere_iff _).1 hf)
  rw [straightenSphere, AddCircle.straightenDiffeomorph_of_forall_eq_add_zsmul hn t hg,
    ← Diffeomorph.diffCongr_symm, MulEquiv.apply_symm_apply]

open scoped TauCeti.DiffeomorphWeakWhitney in
/-- **The straightening retraction of `Diff(S¹)` onto `O(2)`**, for `C^n` diffeomorphisms with
`n ≠ 0`, `n ≤ ∞`, in the weak Whitney topology. Read through the parametrization
`AddCircle.diffeomorphSphere` of `S¹` by `ℝ / ℤ`, a diffeomorphism `f` goes to the isometry
`θ ↦ f 0 ± θ` (`AddCircle.straighteningRetraction`), which is the restriction of a unique
orthogonal transformation (`TauCeti.orthogonalToDiffSphere_diffCircleToOrthogonal`). It is a left
inverse of the reference inclusion (`TauCeti.diffCircleToOrthogonal_orthogonalToDiffSphere`). -/
noncomputable def diffCircleToOrthogonal (hn : n ≠ 0) :
    C(Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n,
      Matrix.orthogonalGroup (Fin 2) ℝ) where
  toFun f := (isClosedEmbedding_orthogonalToDiffSphere 1 n).isEmbedding.toHomeomorph.symm
    ⟨straightenSphere hn 1 f, straightenSphere_one_mem_range hn f⟩
  continuous_toFun := Homeomorph.continuous_symm _ |>.comp <|
    ((continuous_straightenSphere hn).comp (continuous_const.prodMk continuous_id)).subtype_mk _

/-- The orthogonal transformation `diffCircleToOrthogonal hn f` restricts on `S¹` to the
conjugate, by `AddCircle.diffeomorphSphere`, of the straightened conjugate of `f`. -/
theorem orthogonalToDiffSphere_diffCircleToOrthogonal (hn : n ≠ 0)
    (f : Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) :
    orthogonalToDiffSphere 1 n (diffCircleToOrthogonal hn f) =
      Diffeomorph.diffCongr (AddCircle.diffeomorphSphere 1 n)
        (AddCircle.straighteningRetraction hn
          (Diffeomorph.diffCongr (AddCircle.diffeomorphSphere 1 n).symm f)) := by
  have h := congrArg Subtype.val
    ((isClosedEmbedding_orthogonalToDiffSphere 1 n).isEmbedding.toHomeomorph.apply_symm_apply
      ⟨straightenSphere hn 1 f, straightenSphere_one_mem_range hn f⟩)
  rw [Topology.IsEmbedding.toHomeomorph_apply_coe] at h
  rw [AddCircle.coe_straighteningRetraction_apply]
  -- `diffCircleToOrthogonal hn f` is by definition the preimage of `straightenSphere hn 1 f`
  -- under the homeomorphism onto the image, and `straightenSphere` is the conjugated straightening.
  exact h

/-- **The straightening retraction is a retraction**: it is a left inverse of the reference
inclusion `O(2) → Diff(S¹)`. -/
theorem diffCircleToOrthogonal_orthogonalToDiffSphere (hn : n ≠ 0)
    (A : Matrix.orthogonalGroup (Fin 2) ℝ) :
    diffCircleToOrthogonal hn (orthogonalToDiffSphere 1 n A) = A := by
  refine orthogonalToDiffSphere_injective 1 n ?_
  rw [orthogonalToDiffSphere_diffCircleToOrthogonal, AddCircle.coe_straighteningRetraction_apply]
  exact straightenSphere_of_mem_range hn 1 ⟨A, rfl⟩

/-- **`Diff(S¹)` deformation retracts onto `O(2)`.** The straightening homotopy of
`AddCircle.straighteningHomotopy`, transported to `S¹` by `AddCircle.diffeomorphSphere`: a
homotopy in `Diff(S¹)` from the identity to the reference inclusion composed with the retraction
`TauCeti.diffCircleToOrthogonal`, fixing the orthogonal transformations throughout. -/
noncomputable def diffCircleStraighteningHomotopy (hn : n ≠ 0) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n))
      ((continuousOrthogonalToDiffSphere 1 n).comp (diffCircleToOrthogonal hn))
      (Set.range (orthogonalToDiffSphere 1 n)) where
  toFun p := straightenSphere hn p.1 p.2
  continuous_toFun := continuous_straightenSphere hn
  map_zero_left := straightenSphere_zero hn
  map_one_left f := by
    rw [ContinuousMap.comp_apply, continuousOrthogonalToDiffSphere_apply,
      orthogonalToDiffSphere_diffCircleToOrthogonal, AddCircle.coe_straighteningRetraction_apply]
    -- Both sides are the conjugated straightening at time `1`, by definition of `straightenSphere`.
    rfl
  prop' t _ hf := straightenSphere_of_mem_range hn t hf

/-- **`Diff(S¹) ≃ O(2)`.** For `0 < n ≤ ∞`, the reference inclusion of the orthogonal group
`O(2)` into the group of `C^n` diffeomorphisms of the circle `S¹ ⊆ ℝ²`, with the weak Whitney
topology, is a homotopy equivalence, with homotopy inverse the straightening retraction
`TauCeti.diffCircleToOrthogonal`. -/
noncomputable def orthogonalToDiffCircleHomotopyEquiv (hn : n ≠ 0) :
    ContinuousMap.HomotopyEquiv (Matrix.orthogonalGroup (Fin 2) ℝ)
      (Diff (𝓡 1) (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) :=
  .ofDeformationRetraction (continuousOrthogonalToDiffSphere 1 n) (diffCircleToOrthogonal hn)
    (fun A ↦ by rw [continuousOrthogonalToDiffSphere_apply,
      diffCircleToOrthogonal_orthogonalToDiffSphere])
    ⟨(diffCircleStraighteningHomotopy hn).toHomotopy.symm⟩

/-- The homotopy equivalence `O(2) ≃ Diff(S¹)` is the reference inclusion. -/
@[simp]
theorem orthogonalToDiffCircleHomotopyEquiv_toFun (hn : n ≠ 0) :
    (orthogonalToDiffCircleHomotopyEquiv hn).toFun = continuousOrthogonalToDiffSphere 1 n :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun _ _ _ _

/-- The homotopy inverse of `O(2) ≃ Diff(S¹)` is the straightening retraction. -/
@[simp]
theorem orthogonalToDiffCircleHomotopyEquiv_invFun (hn : n ≠ 0) :
    (orthogonalToDiffCircleHomotopyEquiv hn).invFun = diffCircleToOrthogonal hn :=
  ContinuousMap.HomotopyEquiv.ofDeformationRetraction_invFun _ _ _ _

end HomotopyEquiv

end TauCeti
