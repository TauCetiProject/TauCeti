/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.Height

/-!
# The height Hessian on the tangent model of a coadjoint orbit

Let `L` be a Lie algebra with an invariant bilinear form `B`, let `p, X ∈ L` with `⁅X, p⁆ = 0`,
and let `ν = B p`. The height Hessian `h_(p,X)(A, C) = -B(⁅A, p⁆, ⁅C, X⁆)`
(`LinearMap.BilinForm.heightHessian`) has polar form `2 h_(p,X)`
(`LinearMap.BilinForm.polar_toQuadraticMap_heightHessian`), and the stabilizer `L_ν` of `ν` lies
in the radical of its quadratic form
(`LinearMap.BilinForm.lieAnnihilator_le_radical_toQuadraticMap_heightHessian`). So the Hessian
descends to a quadratic form on the algebraic tangent model `L ⧸ L_ν` of the coadjoint orbit
through `ν` (`LinearMap.BilinForm.liftHeightHessian`), the Hessian of the height `f_X` at `p` read
in the quotient coordinates `[A] ↦ ⁅A, p⁆`, with the same indices of inertia
(`LinearMap.BilinForm.sigNeg_liftHeightHessian`, `LinearMap.BilinForm.sigPos_liftHeightHessian`).

In a root-plane decomposition (`TauCeti.IsRootPlaneDecomposition B t α E J`) and for a separating
form, the stabilizer of `ν = B p`, `p ∈ t`, is `t` together with the planes with `α_i(p) = 0`
(`TauCeti.IsRootPlaneDecomposition.lieAnnihilator_eq`), so the orbit has dimension
`dim (L ⧸ L_ν) = ∑ {dim E_i | α_i(p) ≠ 0}`
(`TauCeti.IsRootPlaneDecomposition.finrank_quotient_lieAnnihilator`). The descended Hessian has
nullity `∑ {dim E_i | α_i(p) ≠ 0, α_i(X) = 0}`
(`TauCeti.IsRootPlaneDecomposition.finrank_radical_liftHeightHessian`), so, when all planes are
nonzero, it is nondegenerate exactly when `α_i(X) ≠ 0` for every plane with `α_i(p) ≠ 0`
(`TauCeti.IsRootPlaneDecomposition.nondegenerate_liftHeightHessian_iff`).

These are statements about the algebraic tangent model `L ⧸ L_ν` and its Hessian quadratic form;
comparing them with the Hessian of the height on the orbit as a manifold needs a chart of the
orbit whose differential is the quotient coordinate.

## Main definitions

* `LinearMap.BilinForm.liftHeightHessian`: the height Hessian on the tangent model `L ⧸ L_ν`.

## Main results

* `LinearMap.BilinForm.lieAnnihilator_le_radical_toQuadraticMap_heightHessian`: the height
  Hessian descends to the tangent model `L ⧸ L_ν`.
* `LinearMap.BilinForm.sigPos_liftHeightHessian`, `LinearMap.BilinForm.sigNeg_liftHeightHessian`:
  the descent preserves both indices of inertia.
* `TauCeti.IsRootPlaneDecomposition.lieAnnihilator_eq`,
  `TauCeti.IsRootPlaneDecomposition.finrank_quotient_lieAnnihilator`: the stabilizer and the
  dimension of the orbit.
* `TauCeti.IsRootPlaneDecomposition.mem_of_lie_eq_zero`: the centralizer of an element of `t` at
  which no root vanishes is `t`.
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

/-! ### The descent to the tangent model -/

namespace LinearMap.BilinForm

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {B : LinearMap.BilinForm R L}
  {p X : L}

/-- **The polar form of the height Hessian.** For an invariant form and commuting `p` and `X`, the
polar form of the quadratic form of the height Hessian is `(A, C) ↦ -2 B(⁅A, p⁆, ⁅C, X⁆)`. -/
theorem polar_toQuadraticMap_heightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) (A C : L) :
    polar (B.heightHessian p X).toQuadraticMap A C = -(2 * B ⁅A, p⁆ ⁅C, X⁆) := by
  rw [LinearMap.BilinMap.polar_toQuadraticMap, heightHessian_apply, heightHessian_apply,
    hB.apply_lie_lie_comm hXp C A]
  ring

/-- **The height Hessian descends to the tangent model.** For an invariant form and commuting `p`
and `X`, the stabilizer `L_ν` of `ν = B p` lies in the radical of the quadratic form of the height
Hessian, which is therefore induced by a quadratic form on the algebraic tangent model `L ⧸ L_ν`
of the coadjoint orbit through `ν` (`LinearMap.BilinForm.liftHeightHessian`). -/
theorem lieAnnihilator_le_radical_toQuadraticMap_heightHessian (hB : B.lieInvariant L)
    (hXp : ⁅X, p⁆ = 0) :
    (TauCeti.lieAnnihilator R L (B p)).toSubmodule ≤
      (B.heightHessian p X).toQuadraticMap.radical := by
  intro A hA
  rw [LieSubalgebra.mem_toSubmodule, hB.mem_lieAnnihilator_iff] at hA
  refine mem_radical_iff'.mpr ⟨by simp [hA], fun C ↦ ?_⟩
  have hAC : B ⁅C, p⁆ ⁅A, X⁆ = 0 := by rw [← hB.apply_lie_lie_comm hXp, hA, LinearMap.zero_apply]
  simp only [LinearMap.BilinMap.toQuadraticMap_apply, heightHessian_apply, map_add,
    LinearMap.add_apply, hA, hAC, LinearMap.zero_apply]
  ring

/-- **The height Hessian on the tangent model.** For an invariant form and commuting `p` and `X`,
the quadratic form on the algebraic tangent model `L ⧸ L_ν` of the coadjoint orbit through
`ν = B p` induced by the height Hessian
(`LinearMap.BilinForm.lieAnnihilator_le_radical_toQuadraticMap_heightHessian`). -/
def liftHeightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) :
    QuadraticForm R (L ⧸ (TauCeti.lieAnnihilator R L (B p)).toSubmodule) :=
  (B.heightHessian p X).toQuadraticMap.lift _
    (lieAnnihilator_le_radical_toQuadraticMap_heightHessian hB hXp)

@[simp]
theorem liftHeightHessian_mk (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) (A : L) :
    liftHeightHessian hB hXp (Submodule.Quotient.mk A) = B.heightHessian p X A A :=
  lift_mk _ A

section LinearOrderedField

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] {B : LinearMap.BilinForm K L} {p X : L}

/-- Descending the height Hessian to the tangent model `L ⧸ L_ν` preserves its positive index of
inertia. -/
@[simp]
theorem sigPos_liftHeightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) :
    sigPos (liftHeightHessian hB hXp) = sigPos (B.heightHessian p X).toQuadraticMap :=
  QuadraticForm.sigPos_lift _ _ _

/-- Descending the height Hessian to the tangent model `L ⧸ L_ν` preserves its negative index of
inertia, the Morse index. -/
@[simp]
theorem sigNeg_liftHeightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) :
    sigNeg (liftHeightHessian hB hXp) = sigNeg (B.heightHessian p X).toQuadraticMap :=
  QuadraticForm.sigNeg_lift _ _ _

end LinearOrderedField

end LinearMap.BilinForm

/-! ### The stabilizer and the dimension of the orbit -/

namespace TauCeti

open LinearMap.BilinForm

namespace IsRootPlaneDecomposition

section Domain

variable {R L ι : Type*} [CommRing R] [PartialOrder R] [IsDomain R] [LieRing L] [LieAlgebra R L]
  [Fintype ι] {B : LinearMap.BilinForm R L} {t : Submodule R L} {α : ι → Dual R t}
  {E : ι → Submodule R L} {J : (i : ι) → Module.End R (E i)}

omit [IsDomain R] in
/-- The planes indexed by the complement of `s` span `L` together with `t` and the planes indexed
by `s`. -/
private theorem codisjoint_biSup_compl [DecidableEq ι] (hD : IsRootPlaneDecomposition B t α E J)
    (s : Finset ι) : Codisjoint (t ⊔ ⨆ i ∈ s, E i) (⨆ i ∈ sᶜ, E i) := by
  have hsplit : ⨆ i, E i = (⨆ i ∈ s, E i) ⊔ ⨆ i ∈ sᶜ, E i := by
    rw [← Finset.iSup_union, Finset.union_compl]
    simp
  rw [codisjoint_iff, sup_assoc, ← hsplit, hD.sup_eq_top]

/-- The planes `E_i` with `α_i(p) ≠ 0` meet the stabilizer of `ν = B p` only in `0`, for a
separating invariant form and `p ∈ t`. -/
private theorem disjoint_biSup_lieAnnihilator [DecidableEq R] [DecidableEq ι]
    (hD : IsRootPlaneDecomposition B t α E J) (hB : B.lieInvariant L) (hsep : B.SeparatingLeft)
    (p : t) :
    Disjoint (⨆ i ∈ ({i | α i p = 0} : Finset ι)ᶜ, E i)
      (lieAnnihilator R L (B p)).toSubmodule := by
  set s : Finset ι := {i | α i p = 0}
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
  calc N = ((t ⊔ ⨆ i ∈ s, E i) ⊔ ⨆ i ∈ sᶜ, E i) ⊓ N := by
        rw [codisjoint_iff.mp (hD.codisjoint_biSup_compl s), top_inf_eq]
    _ = t ⊔ ⨆ i ∈ s, E i := by
        rw [sup_inf_assoc_of_le _ hle, (hD.disjoint_biSup_lieAnnihilator hB hsep p).eq_bot,
          sup_bot_eq]

omit [Fintype ι] in
/-- **The centralizer of a regular element.** For a separating invariant form and `X ∈ t` at
which no root vanishes, every element of `L` commuting with `X` lies in `t`: the stabilizer of
`B X` is `t` (`TauCeti.IsRootPlaneDecomposition.lieAnnihilator_eq`). -/
theorem mem_of_lie_eq_zero [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hB : B.lieInvariant L) (hsep : B.SeparatingLeft) {X : t} (hX : ∀ i, α i X ≠ 0) {q : L}
    (h : ⁅(X : L), q⁆ = 0) : q ∈ t := by
  classical
  have := Fintype.ofFinite ι
  have hmem : q ∈ (lieAnnihilator R L (B X)).toSubmodule := by
    rw [LieSubalgebra.mem_toSubmodule, hB.mem_lieAnnihilator_iff, ← lie_skew, h, neg_zero,
      map_zero]
  rw [hD.lieAnnihilator_eq hB hsep X] at hmem
  simpa [hX] using hmem

/-- The planes `E_i` with `α_i(p) ≠ 0` are a complement of the stabilizer of `ν = B p`, for a
separating invariant form and `p ∈ t`. -/
private theorem isCompl_lieAnnihilator [DecidableEq R] [DecidableEq ι]
    (hD : IsRootPlaneDecomposition B t α E J) (hB : B.lieInvariant L) (hsep : B.SeparatingLeft)
    (p : t) : IsCompl (lieAnnihilator R L (B p)).toSubmodule
      (⨆ i ∈ ({i | α i p = 0} : Finset ι)ᶜ, E i) := by
  refine ⟨(hD.disjoint_biSup_lieAnnihilator hB hsep p).symm, ?_⟩
  rw [hD.lieAnnihilator_eq hB hsep p]
  exact hD.codisjoint_biSup_compl _

end Domain

section LinearOrderedField

variable {K L ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L] [Fintype ι]
  {B : LinearMap.BilinForm K L} {t : Submodule K L} {α : ι → Dual K t} {E : ι → Submodule K L}
  {J : (i : ι) → Module.End K (E i)}

omit [IsStrictOrderedRing K] in
/-- **The dimension of the coadjoint orbit through a torus element.** For a separating invariant
form and `p ∈ t`, the algebraic tangent model `L ⧸ L_ν` of the orbit through `ν = B p` has
dimension `∑ {dim E_i | α_i(p) ≠ 0}`. -/
theorem finrank_quotient_lieAnnihilator (hD : IsRootPlaneDecomposition B t α E J)
    (hB : B.lieInvariant L) (hsep : B.SeparatingLeft) (p : t) :
    finrank K (L ⧸ (lieAnnihilator K L (B p)).toSubmodule) =
      ∑ i with α i p ≠ 0, finrank K (E i) := by
  classical
  rw [(Submodule.quotientEquivOfIsCompl _ _ (hD.isCompl_lieAnnihilator hB hsep p)).finrank_eq,
    finrank_biSup_eq_sum_finrank_of_iSupIndep hD.iSupIndep, Finset.compl_filter]

/-- **The nullity of a height on the tangent model.** For a separating invariant form and
`p, X ∈ t`, the radical of the height Hessian induced on the tangent model `L ⧸ L_ν` of the orbit
through `ν = B p` has dimension `∑ {dim E_i | α_i(p) ≠ 0, α_i(X) = 0}`. -/
theorem finrank_radical_liftHeightHessian (hD : IsRootPlaneDecomposition B t α E J)
    (hB : B.lieInvariant L) (hsep : B.SeparatingLeft) (p X : t) :
    finrank K (liftHeightHessian hB (hD.lie_eq_zero X.property p.property)).radical =
      ∑ i with α i p ≠ 0 ∧ α i X = 0, finrank K (E i) := by
  have hrad := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := liftHeightHessian hB (hD.lie_eq_zero X.property p.property))
  rw [sigPos_liftHeightHessian, sigNeg_liftHeightHessian, hD.sigPos_toQuadraticMap_heightHessian,
    hD.sigNeg_toQuadraticMap_heightHessian, hD.finrank_quotient_lieAnnihilator hB hsep] at hrad
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
/-- **Nondegeneracy of a height on the tangent model.** For a separating invariant form, all of
whose root planes are nonzero, and `p, X ∈ t`, the height Hessian induced on the tangent model
`L ⧸ L_ν` of the orbit through `ν = B p` is nondegenerate exactly when `α_i(X) ≠ 0` for every root
plane with `α_i(p) ≠ 0`. In particular it is nondegenerate when no root vanishes at `X`. -/
theorem nondegenerate_liftHeightHessian_iff [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hB : B.lieInvariant L) (hsep : B.SeparatingLeft) (hE : ∀ i, E i ≠ ⊥) (p X : t) :
    (liftHeightHessian hB (hD.lie_eq_zero X.property p.property)).Nondegenerate ↔
      ∀ i, α i p ≠ 0 → α i X ≠ 0 := by
  have := Fintype.ofFinite ι
  have : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [nondegenerate_iff_radical_eq_bot, ← Submodule.finrank_eq_zero,
    hD.finrank_radical_liftHeightHessian hB hsep, Finset.sum_eq_zero_iff]
  simp [Submodule.finrank_eq_zero, hE]

end LinearOrderedField

end IsRootPlaneDecomposition

end TauCeti
