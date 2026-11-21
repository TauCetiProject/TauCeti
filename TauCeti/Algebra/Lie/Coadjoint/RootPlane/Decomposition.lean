/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# The height Hessian of a coadjoint orbit through a root-plane decomposition

Let `L` be a Lie algebra with a bilinear form `B`, and let `p, X ∈ L`. The **height Hessian**
`B.heightHessian p X` is the quadratic form `A ↦ -B(⁅A, p⁆, ⁅A, X⁆)` on `L`
(`LinearMap.BilinForm.heightHessian`, in `TauCeti.Algebra.Lie.Coadjoint.RootPlane`). When `B` is
invariant and `⁅X, p⁆ = 0`, it is the second derivative of `t ↦ B(Ad_(exp tA) p, X)` at `t = 0`
and descends to the algebraic tangent model `L ⧸ L_ν` of the orbit through `ν = B p`
(`LinearMap.BilinForm.liftHeightHessian`). This file sums its one-plane formulas over a whole
decomposition of `L`.

A **root-plane decomposition** (`TauCeti.IsRootPlaneDecomposition B t α E J`) splits `L` as the
direct sum of a commutative subspace `t` and pairwise `B`-orthogonal root planes `E i` of `t`
(`TauCeti.IsRootPlane`) with roots `α i`. For a compact Lie algebra with a positive invariant form
and a maximal torus `t`, these are the real planes of the root decomposition, one for each pair of
roots `±α`. For `p, X ∈ t` the height Hessian has no cross terms between distinct planes and
vanishes on `t`:

`B(⁅H + ∑ vᵢ, p⁆, ⁅H' + ∑ wᵢ, X⁆) = ∑ α_i(p) α_i(X) B(vᵢ, wᵢ)`

(`TauCeti.IsRootPlaneDecomposition.apply_lie_add_sum_lie_add_sum`). So when `B` is positive on the
planes, the Hessian is negative definite on the planes with `α_i(p) α_i(X) > 0`, positive definite
on those with `α_i(p) α_i(X) < 0` and zero on the rest, and Sylvester's law of inertia gives its
indices:

* the **Morse index** `sigNeg = ∑ {dim E_i | α_i(p) α_i(X) > 0}`
  (`TauCeti.IsRootPlaneDecomposition.sigNeg_heightHessian`), that is
  `2 · #{i | α_i(p) α_i(X) > 0}` for planes
  (`TauCeti.IsRootPlaneDecomposition.sigNeg_heightHessian_of_finrank_eq_two`);
* the positive index `sigPos = ∑ {dim E_i | α_i(p) α_i(X) < 0}`
  (`TauCeti.IsRootPlaneDecomposition.sigPos_heightHessian`).

For a separating invariant form the stabilizer of `ν = B p` is `t` together with the planes with
`α_i(p) = 0` (`TauCeti.IsRootPlaneDecomposition.lieAnnihilator_eq`), so the orbit has dimension
`dim (L ⧸ L_ν) = ∑ {dim E_i | α_i(p) ≠ 0}`
(`TauCeti.IsRootPlaneDecomposition.finrank_quotient_lieAnnihilator`). The Hessian descended to
`L ⧸ L_ν` is nondegenerate, when all planes are nonzero, exactly when `α_i(X) ≠ 0` for every
plane with `α_i(p) ≠ 0` (`TauCeti.IsRootPlaneDecomposition.nondegenerate_liftHeightHessian_iff`).
In particular, when no root vanishes at `X` the Hessian on the tangent model is nondegenerate,
and when the planes are indexed by the positive roots `Φ⁺` its index is
`2 · #{α ∈ Φ⁺ | α(p) ≠ 0, α(X) α(p) > 0}`.

These are statements about the algebraic tangent model `L ⧸ L_ν` and its Hessian quadratic form;
comparing them with the Hessian of the height on the orbit as a manifold needs a chart of the
orbit whose differential is the quotient coordinate.

## Main definitions

* `TauCeti.IsRootPlaneDecomposition B t α E J`: `L = t ⊕ ⨁ E_i` with `t` commutative and the
  `E_i` pairwise orthogonal root planes of `t`.

## Main results

* `TauCeti.IsRootPlaneDecomposition.apply_lie_add_sum_lie_add_sum`: the height Hessian in a
  root-plane decomposition.
* `TauCeti.IsRootPlaneDecomposition.sigNeg_heightHessian`,
  `TauCeti.IsRootPlaneDecomposition.sigPos_heightHessian`: its two indices of inertia.
* `TauCeti.IsRootPlaneDecomposition.lieAnnihilator_eq`,
  `TauCeti.IsRootPlaneDecomposition.finrank_quotient_lieAnnihilator`: the stabilizer and the
  dimension of the orbit.
* `TauCeti.IsRootPlaneDecomposition.finrank_radical_liftHeightHessian`,
  `TauCeti.IsRootPlaneDecomposition.nondegenerate_liftHeightHessian_iff`: nullity and
  nondegeneracy of the Hessian on the tangent model.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II (coadjoint orbits and their height functions).
-/

public section

open Module (Dual finrank)
open QuadraticMap

namespace TauCeti

open LinearMap.BilinForm

/-- `L` is the direct sum of a commutative subspace `t` and the pairwise `B`-orthogonal root
planes `E i` of `t`, with roots `α i` and rotations `J i` (`TauCeti.IsRootPlane`). For a compact
Lie algebra with a positive invariant form and a maximal abelian subalgebra `t`, the real planes of
the root decomposition, one for each pair of roots `±α`, form such a decomposition. -/
structure IsRootPlaneDecomposition {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (B : LinearMap.BilinForm R L) (t : Submodule R L) (α : ι → Dual R t) (E : ι → Submodule R L)
    (J : (i : ι) → Module.End R (E i)) : Prop where
  /-- Each `E i` is a root plane of `t` with root `α i` and rotation `J i`. -/
  isRootPlane (i : ι) : IsRootPlane B t (α i) (E i) (J i)
  /-- The subspace `t` is commutative. -/
  lie_eq_zero {H H' : L} : H ∈ t → H' ∈ t → ⁅H, H'⁆ = 0
  /-- Distinct root planes are orthogonal for `B`. -/
  le_orthogonal : Pairwise fun i j ↦ E j ≤ B.orthogonal (E i)
  /-- The root planes are independent. -/
  iSupIndep : _root_.iSupIndep E
  /-- The root planes meet `t` only in `0`. -/
  disjoint : Disjoint t (⨆ i, E i)
  /-- The subspace `t` and the root planes span `L`. -/
  sup_eq_top : t ⊔ ⨆ i, E i = ⊤

namespace IsRootPlaneDecomposition

section CommRing

variable {R L ι : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {B : LinearMap.BilinForm R L} {t : Submodule R L} {α : ι → Dual R t} {E : ι → Submodule R L}
  {J : (i : ι) → Module.End R (E i)}

/-- **The height Hessian in a root-plane decomposition.** For `p, X ∈ t`, `H, H' ∈ t` and
`A = H + ∑ vᵢ`, `C = H' + ∑ wᵢ` with `vᵢ, wᵢ ∈ E i`,
`B(⁅A, p⁆, ⁅C, X⁆) = ∑ α_i(p) α_i(X) B(vᵢ, wᵢ)`: the form behind the height Hessian vanishes on
`t` and has no cross terms between distinct root planes. -/
theorem apply_lie_add_sum_lie_add_sum (hD : IsRootPlaneDecomposition B t α E J) (p X : t)
    {H H' : L} (hH : H ∈ t) (hH' : H' ∈ t) (s : Finset ι) (v w : ∀ i, E i) :
    B ⁅H + ∑ i ∈ s, (v i : L), (p : L)⁆ ⁅H' + ∑ i ∈ s, (w i : L), (X : L)⁆ =
      ∑ i ∈ s, α i p * α i X * B (v i) (w i) := by
  classical
  rw [add_lie, add_lie, hD.lie_eq_zero hH p.property, hD.lie_eq_zero hH' X.property, zero_add,
    zero_add, sum_lie, sum_lie, map_sum B, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [map_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji ↦ ?_]
  · exact (hD.isRootPlane i).apply_lie_lie p X (v i) (w i)
  · exact (hD.isRootPlane i).apply_lie_lie_eq_zero_of_le_orthogonal (hD.isRootPlane j)
      (hD.le_orthogonal hji.symm) p X (v i) (w j)

/-- The height Hessian at `H + ∑ vᵢ`, for `H ∈ t` and `vᵢ ∈ E i`, is
`-∑ α_i(p) α_i(X) B(vᵢ, vᵢ)`. -/
theorem heightHessian_add_sum (hD : IsRootPlaneDecomposition B t α E J) (p X : t) {H : L}
    (hH : H ∈ t) (s : Finset ι) (v : ∀ i, E i) :
    B.heightHessian p X (H + ∑ i ∈ s, (v i : L)) = -∑ i ∈ s, α i p * α i X * B (v i) (v i) := by
  rw [heightHessian_apply, hD.apply_lie_add_sum_lie_add_sum p X hH hH s v v]

/-- The root planes indexed by a finite set `s` are complementary to `t` together with the
remaining root planes. -/
theorem isCompl_biSup (hD : IsRootPlaneDecomposition B t α E J) [Fintype ι] [DecidableEq ι]
    (s : Finset ι) : IsCompl (⨆ i ∈ s, E i) (t ⊔ ⨆ i ∈ sᶜ, E i) := by
  have hsplit : ⨆ i, E i = (⨆ i ∈ s, E i) ⊔ ⨆ i ∈ sᶜ, E i := by
    rw [← Finset.iSup_union, Finset.union_compl]
    simp
  have hdisj : Disjoint (⨆ i ∈ s, E i) (⨆ i ∈ sᶜ, E i) := by
    simpa using hD.iSupIndep.disjoint_biSup_biSup (s := (s : Set ι))
      (t := ((sᶜ : Finset ι) : Set ι)) (by simp [Finset.coe_compl, disjoint_compl_right])
  rw [sup_comm t]
  exact hdisj.isCompl_sup_right_of_isCompl_sup_left ⟨hsplit ▸ hD.disjoint.symm,
    codisjoint_iff.mpr (by rw [← hsplit, sup_comm, hD.sup_eq_top])⟩

end CommRing

section Domain

variable {R L ι : Type*} [CommRing R] [IsDomain R] [LieRing L] [LieAlgebra R L] [Fintype ι]
  {B : LinearMap.BilinForm R L} {t : Submodule R L} {α : ι → Dual R t} {E : ι → Submodule R L}
  {J : (i : ι) → Module.End R (E i)}

/-- **The stabilizer in a root-plane decomposition.** For a separating invariant form and
`p ∈ t`, the stabilizer of `ν = B p` is `t` together with the root planes whose roots vanish at
`p`. -/
theorem lieAnnihilator_eq [DecidableEq R] (hD : IsRootPlaneDecomposition B t α E J)
    (hB : B.lieInvariant L) (hsep : B.SeparatingLeft) (p : t) :
    (lieAnnihilator R L (B p)).toSubmodule = t ⊔ ⨆ i ∈ ({i | α i p = 0} : Finset ι), E i := by
  classical
  set s : Finset ι := {i | α i p = 0}
  set N := (lieAnnihilator R L (B p)).toSubmodule
  have hle : t ⊔ ⨆ i ∈ s, E i ≤ N := by
    refine sup_le (fun H hH ↦ ?_) (iSup₂_le fun i hi ↦ ?_)
    · rw [LieSubalgebra.mem_toSubmodule, hB.mem_lieAnnihilator_iff, hD.lie_eq_zero hH p.property,
        map_zero]
    · exact (hD.isRootPlane i).le_lieAnnihilator hB (by simpa [s] using hi)
  have hdisj : Disjoint (⨆ i ∈ sᶜ, E i) N := by
    refine Submodule.disjoint_def.mpr fun x hxA hxN ↦ ?_
    obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum E x).mp hxA
    rw [LieSubalgebra.mem_toSubmodule, hB.mem_lieAnnihilator_iff] at hxN
    have hlie : ∑ i ∈ sᶜ, ⁅(μ i : L), (p : L)⁆ = 0 := by
      rw [← sum_lie]
      exact hsep _ fun y ↦ by rw [hxN, LinearMap.zero_apply]
    -- Each bracket `⁅μ i, p⁆ = -α_i(p) J μ i` lies in `E i`, so independence kills each of them.
    have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero E).mp hD.iSupIndep sᶜ
      (fun i ↦ ⁅(μ i : L), (p : L)⁆) (fun i _ ↦ by
        rw [(hD.isRootPlane i).lie_left]
        exact neg_mem (Submodule.smul_mem _ _ (J i (μ i)).property)) hlie
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hmem : (μ i : L) ∈ lieAnnihilator R L (B p) := by
      rw [hB.mem_lieAnnihilator_iff, hzero i hi, map_zero]
    rcases ((hD.isRootPlane i).mem_lieAnnihilator_iff hB hsep p (μ i)).mp hmem with h | h
    · exact absurd h (by simpa [s] using hi)
    · simp [h]
  have hcompl := hD.isCompl_biSup sᶜ
  rw [compl_compl] at hcompl
  calc N = ((t ⊔ ⨆ i ∈ s, E i) ⊔ ⨆ i ∈ sᶜ, E i) ⊓ N := by
        rw [hcompl.symm.sup_eq_top, top_inf_eq]
    _ = t ⊔ ⨆ i ∈ s, E i := by
        rw [sup_inf_assoc_of_le _ hle, hdisj.eq_bot, sup_bot_eq]

end Domain

section Field

variable {K L ι : Type*} [Field K] [LieRing L] [LieAlgebra K L] [Fintype ι]
  {B : LinearMap.BilinForm K L} {t : Submodule K L} {α : ι → Dual K t} {E : ι → Submodule K L}
  {J : (i : ι) → Module.End K (E i)}

/-- **The dimension of the coadjoint orbit through a torus element.** For a separating invariant
form and `p ∈ t`, the algebraic tangent model `L ⧸ L_ν` of the orbit through `ν = B p` has
dimension `∑ {dim E_i | α_i(p) ≠ 0}`. -/
theorem finrank_quotient_lieAnnihilator [DecidableEq K] [FiniteDimensional K L]
    (hD : IsRootPlaneDecomposition B t α E J) (hB : B.lieInvariant L) (hsep : B.SeparatingLeft)
    (p : t) :
    finrank K (L ⧸ (lieAnnihilator K L (B p)).toSubmodule) =
      ∑ i with α i p ≠ 0, finrank K (E i) := by
  classical
  rw [hD.lieAnnihilator_eq hB hsep p, ← compl_compl ({i | α i p = 0} : Finset ι),
    (Submodule.quotientEquivOfIsCompl _ _ (hD.isCompl_biSup _).symm).finrank_eq,
    finrank_biSup_eq_sum_finrank_of_iSupIndep hD.iSupIndep, Finset.compl_filter]

end Field

section LinearOrderedField

variable {K L ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] [Fintype ι]
  {B : LinearMap.BilinForm K L} {t : Submodule K L} {α : ι → Dual K t} {E : ι → Submodule K L}
  {J : (i : ι) → Module.End K (E i)}

/-- **The Morse index of a height in a root-plane decomposition.** If `B` is positive on the root
planes, then for `p, X ∈ t` the negative index of inertia of the height Hessian is
`∑ {dim E_i | α_i(p) α_i(X) > 0}`. -/
theorem sigNeg_heightHessian (hD : IsRootPlaneDecomposition B t α E J)
    (hpos : ∀ i, ∀ v ∈ E i, v ≠ 0 → 0 < B v v) (p X : t) :
    sigNeg (B.heightHessian p X) = ∑ i with 0 < α i p * α i X, finrank K (E i) := by
  classical
  set s : Finset ι := {i | 0 < α i p * α i X}
  have hnonneg (i : ι) (v : E i) : 0 ≤ B v v := by
    by_cases hv : (v : L) = 0
    · simp [hv]
    · exact (hpos i v v.property hv).le
  rw [QuadraticForm.sigNeg_eq_finrank_of_isCompl_of_negDef _ (hD.isCompl_biSup s) ?_ ?_,
    finrank_biSup_eq_sum_finrank_of_iSupIndep hD.iSupIndep]
  · rintro ⟨x, hx⟩ hx0
    obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum E x).mp hx
    have hQ := hD.heightHessian_add_sum p X t.zero_mem s μ
    rw [zero_add] at hQ
    rw [QuadraticMap.restrict_apply, _root_.neg_apply, hQ, neg_neg]
    obtain ⟨i, hi, hμi⟩ : ∃ i ∈ s, (μ i : L) ≠ 0 := by
      by_contra! h
      exact hx0 (Subtype.ext (by simp [Finset.sum_eq_zero h]))
    have hmem (j : ι) (hj : j ∈ s) : 0 < α j p * α j X := by simpa [s] using hj
    exact Finset.sum_pos' (fun j hj ↦ mul_nonneg (hmem j hj).le (hnonneg j _))
      ⟨i, hi, mul_pos (hmem i hi) (hpos i _ (μ i).property hμi)⟩
  · intro x hx
    obtain ⟨h, hh, d, hd, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum E d).mp hd
    rw [hD.heightHessian_add_sum p X hh, neg_nonneg]
    have hmem (i : ι) (hi : i ∈ sᶜ) : α i p * α i X ≤ 0 := by simpa [s] using hi
    exact Finset.sum_nonpos fun i hi ↦ mul_nonpos_of_nonpos_of_nonneg (hmem i hi) (hnonneg i _)

/-- **The positive index of a height in a root-plane decomposition.** If `B` is positive on the
root planes, then for `p, X ∈ t` the positive index of inertia of the height Hessian is
`∑ {dim E_i | α_i(p) α_i(X) < 0}`. -/
theorem sigPos_heightHessian (hD : IsRootPlaneDecomposition B t α E J)
    (hpos : ∀ i, ∀ v ∈ E i, v ≠ 0 → 0 < B v v) (p X : t) :
    sigPos (B.heightHessian p X) = ∑ i with α i p * α i X < 0, finrank K (E i) := by
  rw [← sigNeg_neg, ← heightHessian_neg_right, ← Submodule.coe_neg,
    hD.sigNeg_heightHessian hpos p (-X)]
  simp

/-- **The Morse index of a height on root planes.** If the root planes are planes and `B` is
positive on them, then for `p, X ∈ t` the negative index of inertia of the height Hessian is
`2 · #{i | α_i(p) α_i(X) > 0}`. -/
theorem sigNeg_heightHessian_of_finrank_eq_two (hD : IsRootPlaneDecomposition B t α E J)
    (hpos : ∀ i, ∀ v ∈ E i, v ≠ 0 → 0 < B v v) (h2 : ∀ i, finrank K (E i) = 2) (p X : t) :
    sigNeg (B.heightHessian p X) = 2 * ({i | 0 < α i p * α i X} : Finset ι).card := by
  rw [hD.sigNeg_heightHessian hpos, Finset.sum_congr rfl fun i _ ↦ h2 i, Finset.sum_const,
    smul_eq_mul, mul_comm]

/-- **The nullity of a height on the tangent model.** For a separating invariant form, positive
on the root planes, and `p, X ∈ t`, the radical of the height Hessian induced on the tangent model
`L ⧸ L_ν` of the orbit through `ν = B p` has dimension
`∑ {dim E_i | α_i(p) ≠ 0, α_i(X) = 0}`. -/
theorem finrank_radical_liftHeightHessian (hD : IsRootPlaneDecomposition B t α E J)
    (hpos : ∀ i, ∀ v ∈ E i, v ≠ 0 → 0 < B v v) (hB : B.lieInvariant L)
    (hsep : B.SeparatingLeft) (p X : t) :
    finrank K (liftHeightHessian hB (hD.lie_eq_zero X.property p.property)).radical =
      ∑ i with α i p ≠ 0 ∧ α i X = 0, finrank K (E i) := by
  have hrad := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := liftHeightHessian hB (hD.lie_eq_zero X.property p.property))
  rw [LinearMap.BilinForm.liftHeightHessian] at hrad ⊢
  rw [QuadraticForm.sigPos_lift, QuadraticForm.sigNeg_lift,
    hD.sigPos_heightHessian hpos, hD.sigNeg_heightHessian hpos,
    hD.finrank_quotient_lieAnnihilator hB hsep] at hrad
  -- Each plane with `α_i(p) ≠ 0` is counted by exactly one of the three sums.
  have hsum : (∑ i with α i p * α i X < 0, finrank K (E i)) +
      (∑ i with 0 < α i p * α i X, finrank K (E i)) +
      ∑ i with α i p ≠ 0 ∧ α i X = 0, finrank K (E i) =
        ∑ i with α i p ≠ 0, finrank K (E i) := by
    simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases eq_or_ne (α i p) 0 with hp | hp
    · simp [hp]
    rcases eq_or_ne (α i X) 0 with hX | hX
    · simp [hp, hX]
    rcases (mul_ne_zero hp hX).lt_or_gt with h | h
    · simp [hp, hX, h, h.not_gt]
    · simp [hp, hX, h, h.not_gt]
  omega

omit [Fintype ι] in
/-- **Nondegeneracy of a height on the tangent model.** For a separating invariant form, positive
on the root planes, all of which are nonzero, and `p, X ∈ t`, the height Hessian induced on the
tangent model `L ⧸ L_ν` of the orbit through `ν = B p` is nondegenerate exactly when `α_i(X) ≠ 0`
for every root plane with `α_i(p) ≠ 0`. In particular it is nondegenerate when no root vanishes at
`X`. -/
theorem nondegenerate_liftHeightHessian_iff [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hpos : ∀ i, ∀ v ∈ E i, v ≠ 0 → 0 < B v v) (hB : B.lieInvariant L)
    (hsep : B.SeparatingLeft) (hE : ∀ i, E i ≠ ⊥) (p X : t) :
    (liftHeightHessian hB (hD.lie_eq_zero X.property p.property)).Nondegenerate ↔
      ∀ i, α i p ≠ 0 → α i X ≠ 0 := by
  have := Fintype.ofFinite ι
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero,
    hD.finrank_radical_liftHeightHessian hpos hB hsep, Finset.sum_eq_zero_iff]
  simp [Submodule.finrank_eq_zero, hE]

end LinearOrderedField

end IsRootPlaneDecomposition

end TauCeti
