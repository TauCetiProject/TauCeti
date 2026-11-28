/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Isometry
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic

/-!
# The adelic unitary group in the adelic matrices

Let `E` be a CM field with infinite adeles `E_∞`, finite adeles `𝔸_f` and adeles
`𝔸 = E_∞ × 𝔸_f`, let `s` be a sign vector, and let `G(s) = G_∞(s) × G_f` be the adelic unitary
group, where `G_∞(s) = U(diag s)(E_∞)` and `G_f = U(1_n)(𝔸_f)`. This file proves two topological
facts about `G(s)`:

* `g ↦` (the adelic matrix of `g`) is a closed embedding of `G(s)` in `M_n(𝔸)`. This identifies
  the topology of `G(s)`, which is that of the pairs `(g, g⁻¹)` in `GL_n(E_∞) × GL_n(𝔸_f)`, with
  the subspace topology of the matrices: the inverse of an element of a unitary group is a
  continuous function of the element.
* For the definite signs `s = (1, …, 1)`, the archimedean group `G_∞(1) = U(n)(E_∞)` is compact,
  as the entries of a unitary matrix have absolute value at most one at every infinite place, so
  compact subsets of `G_f` have compact preimages in `G(1)`.

## Main definitions

* `TauCeti.adelicUnitaryGroup.toAdeleMatrix E s`: the adelic matrix `G(s) →* M_n(𝔸)`.

## Main results

* `TauCeti.adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix`: the adelic matrix is a closed
  embedding.
* `TauCeti.norm_apply_le_one_of_star_mul_self_eq_one`: the entries of a unitary matrix over the
  infinite adeles have norm at most one at every infinite place, and
  `TauCeti.isCompact_infiniteAdelicUnitaryGroup_one`: `G_∞(1)` is compact, so that
  `TauCeti.adelicUnitaryGroup.isCompact_preimage_finitePart`: compact subsets of `G_f` have compact
  preimages in `G(1)`.

## References

* V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory*, Academic Press (1994),
  Chapter 5.

## Attribution

The closed embedding statement is that of `New.G.isClosedEmbedding_adeleMatrix` in
`src/Lib/Adelic/Unitary/WeakApproximation.lean` of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC); the formalization here is independent of that code.
-/

public section
noncomputable section

open Matrix NumberField Topology
open scoped NumberField.AdeleRing

namespace TauCeti

/-! ### The archimedean unitary group of the definite form is compact -/

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

variable (E ι) in
/-- **The archimedean unitary group of the definite form is compact**: `G_∞(1) = U(n)(E_∞)` is a
closed subset of the matrices over the infinite adeles, whose entries have norm at most one at
every infinite place (`norm_apply_le_one_of_star_mul_self_eq_one`). -/
theorem isCompact_infiniteAdelicUnitaryGroup_one :
    IsCompact (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ) : Set (GL ι (InfiniteAdeleRing E))) := by
  have hball (w : InfinitePlace E) : IsCompact (Metric.closedBall (0 : w.Completion) 1) :=
    haveI := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    isCompact_closedBall 0 1
  have hd : (diagonal fun i ↦ (((1 : ι → ℤˣ) i : ℤ) : InfiniteAdeleRing E)) = 1 := by simp
  have he := unitaryGroupOf.isClosedEmbedding_val
    (A := diagonal fun i ↦ (((1 : ι → ℤˣ) i : ℤ) : InfiniteAdeleRing E)) (hd ▸ isUnit_one)
  have hB : IsCompact (Set.matrix (m := ι) (n := ι) (Set.univ.pi fun w : InfinitePlace E ↦
      Metric.closedBall (0 : w.Completion) 1 : Set (InfiniteAdeleRing E))) :=
    (isCompact_univ_pi hball).matrix
  refine isCompact_iff_compactSpace.2 (isCompact_univ_iff.1 ?_)
  convert he.isCompact_preimage hB using 1
  refine (Set.eq_univ_of_forall fun g ↦ ?_).symm
  have hg : star ((g : GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) *
      ((g : GL ι (InfiniteAdeleRing E)) : Matrix ι ι (InfiniteAdeleRing E)) = 1 := by
    simpa [hd] using mem_unitaryGroupOf_iff.1 g.property
  rw [Set.mem_preimage, Set.mem_matrix]
  intro i j w _
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_apply_le_one_of_star_mul_self_eq_one hg i j w

instance : CompactSpace (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ)) :=
  isCompact_iff_compactSpace.mp (isCompact_infiniteAdelicUnitaryGroup_one E ι)

end Compact

/-! ### The adelic matrix -/

section AdeleMatrix

variable (E : Type*) [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- The **adelic matrix** of an element `g = (g_∞, g_f)` of the adelic unitary group `G(s)`: the
matrix in `M_n(𝔸)`, `𝔸 = E_∞ × 𝔸_f`, whose entry `(i, j)` is the adele `(g_∞ i j, g_f i j)`. It
is multiplicative, and a closed embedding (`isClosedEmbedding_toAdeleMatrix`). -/
def adelicUnitaryGroup.toAdeleMatrix (s : ι → ℤˣ) : adelicUnitaryGroup E s →* Matrix ι ι 𝔸[E] :=
  ((Matrix.prodRingEquiv ι (InfiniteAdeleRing E) 𝔸ᶠ[E]).symm.toMonoidHom.comp
    ((Units.coeHom _).prodMap (Units.coeHom _))).comp (adelicUnitaryGroup E s).subtype

variable {E}

/-- The archimedean component of the entry `(i, j)` of the adelic matrix of `g` is `g_∞ i j`. -/
@[simp]
theorem adelicUnitaryGroup.fst_toAdeleMatrix_apply {s : ι → ℤˣ} (g : adelicUnitaryGroup E s)
    (i j : ι) :
    (adelicUnitaryGroup.toAdeleMatrix E s g i j).1 =
      ((g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).1 : Matrix ι ι (InfiniteAdeleRing E)) i j :=
  (rfl)

/-- The finite component of the entry `(i, j)` of the adelic matrix of `g` is `g_f i j`. -/
@[simp]
theorem adelicUnitaryGroup.snd_toAdeleMatrix_apply {s : ι → ℤˣ} (g : adelicUnitaryGroup E s)
    (i j : ι) :
    (adelicUnitaryGroup.toAdeleMatrix E s g i j).2 =
      ((g : GL ι (InfiniteAdeleRing E) × GL ι 𝔸ᶠ[E]).2 : Matrix ι ι 𝔸ᶠ[E]) i j :=
  (rfl)

/-- **`G(s)` is a closed subset of the adelic matrices**: the adelic matrix
`G(s) → M_n(𝔸)` is a closed embedding. The unitary groups `G_∞(s)` and `G_f` are closed subsets
of the matrices over `E_∞` and over `𝔸_f` with the subspace topology
(`Matrix.unitaryGroupOf.isClosedEmbedding_val`), and `M_n(𝔸)` is `M_n(E_∞) × M_n(𝔸_f)`. -/
theorem adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix (s : ι → ℤˣ) :
    IsClosedEmbedding (adelicUnitaryGroup.toAdeleMatrix E s) := by
  have hs : IsUnit (diagonal fun i ↦ ((s i : ℤ) : InfiniteAdeleRing E)) :=
    isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i ↦ (s i).isUnit.map (Int.castRingHom _))
  have hf := unitaryGroupOf.isClosedEmbedding_val (A := (1 : Matrix ι ι 𝔸ᶠ[E])) isUnit_one
  rw [unitaryGroupOf_one] at hf
  -- `M_n(E_∞ × 𝔸_f)` is homeomorphic to `M_n(E_∞) × M_n(𝔸_f)`.
  let e : Matrix ι ι 𝔸[E] ≃ₜ Matrix ι ι (InfiniteAdeleRing E) × Matrix ι ι 𝔸ᶠ[E] :=
    { Matrix.prodEquiv ι ι (InfiniteAdeleRing E) 𝔸ᶠ[E] with
      continuous_toFun := (continuous_id.matrix_map continuous_fst).prodMk
        (continuous_id.matrix_map continuous_snd)
      continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦
        ((continuous_apply j).comp ((continuous_apply i).comp continuous_fst)).prodMk
          ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)) }
  exact e.symm.isClosedEmbedding.comp
    (((unitaryGroupOf.isClosedEmbedding_val hs).prodMap hf).comp
      (Homeomorph.Set.prod _ _).isClosedEmbedding)

/-- The adelic matrix `G(s) → M_n(𝔸)` is continuous. -/
@[fun_prop]
theorem adelicUnitaryGroup.continuous_toAdeleMatrix (s : ι → ℤˣ) :
    Continuous (adelicUnitaryGroup.toAdeleMatrix E s) :=
  (adelicUnitaryGroup.isClosedEmbedding_toAdeleMatrix s).continuous

/-- **For definite signs, compact sets have compact preimages in `G(1)`**: the preimage in
`G(1) = G_∞(1) × G_f` of a compact subset `S` of `G_f` is `G_∞(1) × S`, which is compact as
`G_∞(1)` is (`isCompact_infiniteAdelicUnitaryGroup_one`), so that the projection to `G_f` is a
proper map. -/
theorem adelicUnitaryGroup.isCompact_preimage_finitePart {S : Set (finiteAdelicUnitaryGroup E ι)}
    (hS : IsCompact S) : IsCompact (adelicUnitaryGroup.finitePart E (1 : ι → ℤˣ) ⁻¹' S) := by
  -- Through `G(1) ≃ₜ G_∞(1) × G_f`, the finite component is the second projection.
  let e := Homeomorph.Set.prod (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ) :
    Set (GL ι (InfiniteAdeleRing E))) (finiteAdelicUnitaryGroup E ι : Set (GL ι 𝔸ᶠ[E]))
  have he : ⇑(adelicUnitaryGroup.finitePart E (1 : ι → ℤˣ)) = Prod.snd ∘ e :=
    funext fun g ↦ Subtype.ext (adelicUnitaryGroup.coe_finitePart g)
  have : CompactSpace (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ) :
      Set (GL ι (InfiniteAdeleRing E))) :=
    inferInstanceAs (CompactSpace (infiniteAdelicUnitaryGroup E (1 : ι → ℤˣ)))
  rw [he]
  exact e.isCompact_preimage.2 (isProperMap_snd_of_compactSpace.isCompact_preimage hS)

end AdeleMatrix

end TauCeti
