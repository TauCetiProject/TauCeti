/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
public import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Field.ProperSpace
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic

/-!
# Compactness of the archimedean unitary group of a definite form

Let `E` be a CM field with infinite adeles `E_∞` and finite adeles `𝔸_f`, let `s` be a sign
vector, and let `G(s) = G_∞(s) × G_f` be the adelic unitary group, where `G_∞(s) = U(diag s)(E_∞)`
and `G_f = U(1_n)(𝔸_f)`.

* For definite signs, all equal to a common sign `ε = ±1`, the form `diag(s) = ε • 1_n` has the
  same unitary group as `1_n`, and `G_∞(s) = U(n)(E_∞)` is compact: the entries of a unitary
  matrix have absolute value at most one at every infinite place.
* Whenever `G_∞(s)` is compact, the projection `G(s) → G_f` is a proper map, so in particular
  compact subsets of `G_f` have compact preimages in `G(s)`.

## Main results

* `TauCeti.norm_apply_le_one_of_star_mul_self_eq_one`: the entries of a unitary matrix over the
  infinite adeles have norm at most one at every infinite place.
* `TauCeti.isCompact_infiniteAdelicUnitaryGroup_of_forall_eq`: `G_∞(s)` is compact for definite
  signs, so that it is a compact space for the signs `(1, …, 1)`.
* `TauCeti.adelicUnitaryGroup.isProperMap_finitePart`: if `G_∞(s)` is compact, the projection
  `G(s) → G_f` is proper.

## References

* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.
-/

public section
noncomputable section

open Matrix NumberField Topology
open scoped NumberField.AdeleRing

namespace TauCeti

/-! ### The archimedean unitary group of a definite form is compact -/

section Compact

variable {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E] {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- **The entries of a unitary matrix over the infinite adeles have norm at most one.** If
`M* M = 1` for a square matrix `M` over the infinite adeles of a CM field, then every entry of `M`
has norm at most one at every infinite place `w`: read in `ℂ` through the embedding attached to
`w`, which turns conjugation into complex conjugation, `M` becomes a unitary complex matrix
(`entry_norm_bound_of_unitary`). -/
theorem norm_apply_le_one_of_star_mul_self_eq_one {M : Matrix ι ι (InfiniteAdeleRing E)}
    (hM : star M * M = 1) (i j : ι) (w : InfinitePlace E) : ‖M i j w‖ ≤ 1 := by
  -- Evaluation at `w` followed by the embedding `E_w → ℂ`, as a ring homomorphism.
  let ψ : InfiniteAdeleRing E →+* ℂ :=
    (InfinitePlace.Completion.extensionEmbedding w).comp (Pi.evalRingHom _ w)
  have hψ : Function.Semiconj ψ star star := fun a ↦
    InfiniteAdeleRing.extensionEmbedding_star_apply a w
  have hU : M.map ψ ∈ unitaryGroup ι ℂ := by
    rw [mem_unitaryGroup_iff']
    calc star (M.map ψ) * M.map ψ = (star M * M).map ψ := by
          rw [star_eq_conjTranspose, star_eq_conjTranspose, ← conjTranspose_map ψ hψ,
            Matrix.map_mul]
      _ = 1 := by rw [hM, Matrix.map_one ψ (map_zero ψ) (map_one ψ)]
  calc ‖M i j w‖ = ‖M.map ψ i j‖ :=
        ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) (M i j w)).symm
    _ ≤ 1 := entry_norm_bound_of_unitary hU i j

variable (E) in
/-- **The archimedean unitary group of a definite form is compact**: if all the signs `s i` are
equal to a common sign `ε`, then `diag(s) = ε • 1_n`, so `G_∞(s) = U(n)(E_∞)` is a closed subset of
the matrices over the infinite adeles whose entries have norm at most one at every infinite place
(`norm_apply_le_one_of_star_mul_self_eq_one`). -/
theorem isCompact_infiniteAdelicUnitaryGroup_of_forall_eq {s : ι → ℤˣ} (ε : ℤˣ)
    (hs : ∀ i, s i = ε) :
    IsCompact (infiniteAdelicUnitaryGroup E s : Set (GL ι (InfiniteAdeleRing E))) := by
  have hball (w : InfinitePlace E) : IsCompact (Metric.closedBall (0 : w.Completion) 1) :=
    haveI := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    isCompact_closedBall 0 1
  have hd : (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) =
      ((ε : ℤ) : InfiniteAdeleRing E) • (1 : Matrix ι ι (InfiniteAdeleRing E)) := by
    rw [smul_one_eq_diagonal]
    simp only [hs]
  have he := unitaryGroupOf.isClosedEmbedding_val
    (isUnit_diagonal_intCast_units (R := InfiniteAdeleRing E) s)
  have hB : IsCompact (Set.matrix (m := ι) (n := ι) (Set.univ.pi fun w : InfinitePlace E ↦
      Metric.closedBall (0 : w.Completion) 1 : Set (InfiniteAdeleRing E))) :=
    (isCompact_univ_pi hball).matrix
  refine isCompact_iff_compactSpace.2 (isCompact_univ_iff.1 ?_)
  convert he.isCompact_preimage hB using 1
  refine (Set.eq_univ_of_forall fun g ↦ ?_).symm
  -- As `ε` is a unit, `g* (ε • 1) g = ε • 1` gives `g* g = 1`.
  have hg : star ((g : GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) *
      ((g : GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) = 1 := by
    have h := mem_unitaryGroupOf_iff.1 g.property
    rw [hd, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h
    exact ((ε.isUnit.map (Int.castRingHom (InfiniteAdeleRing E))).smul_left_cancel).1 h
  rw [Set.mem_preimage, Set.mem_matrix]
  intro i j w _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_apply_le_one_of_star_mul_self_eq_one hg i j w

/-- For the signs `(1, …, 1)`, `G_∞(1) = U(n)(E_∞)` is a compact space. -/
instance : CompactSpace (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ)) :=
  isCompact_iff_compactSpace.mp
    (isCompact_infiniteAdelicUnitaryGroup_of_forall_eq E 1 fun _ ↦ rfl)

end Compact

/-! ### The projection to the finite part is proper -/

section Proper

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- **If `G_∞(s)` is compact, the projection `G(s) → G_f` is proper**: through the homeomorphism
`G(s) ≃ₜ G_∞(s) × G_f` it is the second projection, which is proper as the first factor is
compact. In particular compact subsets of `G_f` have compact preimages in `G(s)`. -/
theorem adelicUnitaryGroup.isProperMap_finitePart (s : ι → ℤˣ)
    [CompactSpace (infiniteAdelicUnitaryGroup E s)] :
    IsProperMap (adelicUnitaryGroup.finitePart E s) := by
  let e := Homeomorph.Set.prod (infiniteAdelicUnitaryGroup E s : Set (GL ι (InfiniteAdeleRing E)))
    (finiteAdelicUnitaryGroup E ι : Set (GL ι 𝔸ᶠ[E]))
  have he : ⇑(adelicUnitaryGroup.finitePart E s) = Prod.snd ∘ e :=
    funext fun g ↦ Subtype.ext (adelicUnitaryGroup.coe_finitePart g)
  have : CompactSpace (infiniteAdelicUnitaryGroup E s : Set (GL ι (InfiniteAdeleRing E))) :=
    inferInstanceAs (CompactSpace (infiniteAdelicUnitaryGroup E s))
  rw [he]
  exact isProperMap_snd_of_compactSpace.comp e.isProperMap

end Proper

end TauCeti
