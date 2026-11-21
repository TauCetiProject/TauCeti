/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.NormalForm
import TauCeti.Analysis.InnerProductSpace.Spectral.Relative

/-!
# Existence of root-plane decompositions

Let `L` be a finite-dimensional real Lie algebra with a symmetric positive definite bilinear form
`B` which is invariant, `B ⁅x, y⁆ z = -B y ⁅x, z⁆`, as for the Lie algebra of a compact Lie group
with an `Ad`-invariant inner product. Let `t` be a commutative subspace of `L`, such as the Lie
algebra of a torus. The maps `ad H`, for `H ∈ t`, are then pairwise commuting and skew for `B`.

This file proves that `L` splits as a `B`-orthogonal direct sum

`L = 𝔷(t) ⊕ E₁ ⊕ ⋯ ⊕ E_r`

of the centralizer `𝔷(t) = {x | ⁅H, x⁆ = 0 for all H ∈ t}` and finitely many planes `E_k`, each a
**root plane** of `t` (`TauCeti.IsRootPlane B t α_k E_k J_k`): `J_k` is a `B`-skew complex
structure on `E_k` and every `H ∈ t` acts on `E_k` by `ad H = α_k(H) J_k`, for a nonzero linear
functional `α_k` on `t` (`TauCeti.exists_isInternal_isRootPlane`). These are the real root planes
and the real roots of `t`; a root may occur on several planes.

This is the real form of the weight decomposition of the complexified adjoint action: over `ℂ`
each plane `E_k ⊗ ℂ` is the sum of the weight lines of `±i α_k`. For the Lie algebra of a maximal
torus of a compact Lie group, the centralizer `𝔷(t)` is `t` itself, which gives the root-plane
decomposition `𝔤 = t ⊕ ⨁ E_k` (`TauCeti.Lie.IsMaximalTorus.exists_isInternal_isRootPlane`, in
`TauCeti.Geometry.Lie.Subgroup.Torus.RootPlane`). The formulas of
`TauCeti.Algebra.Lie.Coadjoint.RootPlane` for the Kirillov–Kostant–Souriau form and the height
Hessians of coadjoint orbits through `t` take such planes as input.

## Main results

* `TauCeti.exists_isInternal_isRootPlane`: a commutative subspace `t` of a Lie algebra with a
  positive definite invariant form splits the Lie algebra into the centralizer of `t` and
  pairwise orthogonal two-dimensional root planes with nonzero roots.

## Implementation notes

The proof transports the problem to Euclidean space through a linear isometry from `B`
(`LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply`) and applies the real normal
form of a commuting linear family of skew-symmetric maps
(`TauCeti.exists_orthonormal_apply_eq_smul_of_skew_of_linearMap`) to `H ↦ ad H`. The planes are
spanned by the images `q_k, p_k` of its orthonormal pairs, and `J_k` is the quarter turn
`v ↦ B(q_k, v) p_k - B(p_k, v) q_k`.

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer, 1985, Chapter IV, § 1 and Chapter V, § 1 (the real root
  decomposition of a compact Lie algebra).
-/

public section

noncomputable section

open Module (Dual finrank)
open scoped RealInnerProductSpace Function

namespace TauCeti

section Plane

variable {L : Type*} [AddCommGroup L] [Module ℝ L] {B : LinearMap.BilinForm ℝ L}

/-- The quarter turn `v ↦ B(q, v) p - B(p, v) q` of a `B`-orthonormal pair `(q, p)`, the complex
structure of a root plane spanned by `q` and `p`. -/
private def quarterTurn (B : LinearMap.BilinForm ℝ L) (q p : L) : L →ₗ[ℝ] L :=
  (B q).smulRight p - (B p).smulRight q

private theorem quarterTurn_apply (q p v : L) :
    quarterTurn B q p v = B q v • p - B p v • q :=
  rfl

private theorem quarterTurn_mem_span (q p v : L) :
    quarterTurn B q p v ∈ Submodule.span ℝ {q, p} :=
  Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The quarter turn of a pair is skew for a symmetric `B`. -/
private theorem apply_quarterTurn (hB : B.IsSymm) (q p v w : L) :
    B (quarterTurn B q p v) w = -B v (quarterTurn B q p w) := by
  simp only [quarterTurn_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hB.eq v p, hB.eq v q]
  ring

private theorem quarterTurn_apply_left {q p : L} (hqq : B q q = 1) (hpq : B p q = 0) :
    quarterTurn B q p q = p := by
  simp [quarterTurn_apply, hqq, hpq]

private theorem quarterTurn_apply_right {q p : L} (hqp : B q p = 0) (hpp : B p p = 1) :
    quarterTurn B q p p = -q := by
  simp [quarterTurn_apply, hqp, hpp]

variable {q p : L} (hqq : B q q = 1) (hqp : B q p = 0) (hpq : B p q = 0) (hpp : B p p = 1)
include hqq hqp hpq hpp

/-- The quarter turn of a `B`-orthonormal pair squares to `-1` on the plane of the pair. -/
private theorem quarterTurn_quarterTurn {v : L} (hv : v ∈ Submodule.span ℝ {q, p}) :
    quarterTurn B q p (quarterTurn B q p v) = -v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  simp only [map_add, map_smul, quarterTurn_apply_left hqq hpq, quarterTurn_apply_right hqp hpp,
    smul_neg, map_neg]
  abel

/-- A `B`-orthonormal pair spans a plane. -/
private theorem finrank_span_pair : finrank ℝ (Submodule.span ℝ {q, p}) = 2 := by
  have hli : LinearIndependent ℝ ![q, p] := by
    refine LinearIndependent.pair_iff.2 fun s u h ↦ ⟨?_, ?_⟩
    · simpa [hqq, hqp] using congrArg (B q) h
    · simpa [hpq, hpp] using congrArg (B p) h
  rw [← Matrix.range_cons_cons_empty q p ![], finrank_span_eq_card hli, Fintype.card_fin]

end Plane

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {r : ℕ} {q p : Fin r → E}

/-- The summands of the real normal form: the orthogonal complement of the planes, and the
planes `span(q k, p k)`. -/
private def planeFamily (q p : Fin r → E) (o : Option (Fin r)) : Submodule ℝ E :=
  o.elim (Submodule.span ℝ (Set.range (Sum.elim q p)))ᗮ fun k ↦ Submodule.span ℝ {q k, p k}

private theorem span_pair_le_span_range (k : Fin r) :
    Submodule.span ℝ {q k, p k} ≤ Submodule.span ℝ (Set.range (Sum.elim q p)) :=
  Submodule.span_mono <| Set.insert_subset ⟨.inl k, rfl⟩ <|
    Set.singleton_subset_iff.2 ⟨.inr k, rfl⟩

private theorem pairwise_isOrtho_planeFamily (hon : Orthonormal ℝ (Sum.elim q p)) :
    Pairwise ((· ⟂ ·) on (planeFamily q p)) := by
  rintro (_ | k) (_ | l) hkl
  · exact absurd rfl hkl
  · exact (Submodule.isOrtho_orthogonal_left _).mono_right (span_pair_le_span_range l)
  · exact (Submodule.isOrtho_orthogonal_right _).mono_left (span_pair_le_span_range k)
  · have hkl : k ≠ l := fun h ↦ hkl (congrArg some h)
    refine Submodule.isOrtho_span.2 ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro u (rfl | rfl) v (rfl | rfl)
    · exact hon.2 (i := .inl k) (j := .inl l) (by simpa using hkl)
    · exact hon.2 (i := .inl k) (j := .inr l) (by simp)
    · exact hon.2 (i := .inr k) (j := .inl l) (by simp)
    · exact hon.2 (i := .inr k) (j := .inr l) (by simpa using hkl)

private theorem isInternal_planeFamily [FiniteDimensional ℝ E]
    (hon : Orthonormal ℝ (Sum.elim q p)) : DirectSum.IsInternal (planeFamily q p) := by
  classical
  refine (OrthogonalFamily.isInternal_iff
    (orthogonalFamily_iff_pairwise.2 (pairwise_isOrtho_planeFamily hon))).2 ?_
  rw [Submodule.orthogonal_eq_bot_iff, eq_top_iff,
    ← Submodule.sup_orthogonal_of_hasOrthogonalProjection
      (K := Submodule.span ℝ (Set.range (Sum.elim q p)))]
  refine sup_le (Submodule.span_le.2 ?_) (le_iSup (planeFamily q p) none)
  rintro _ ⟨k | k, rfl⟩ <;>
    exact le_iSup (planeFamily q p) (some k) (Submodule.subset_span (by simp))

end Euclidean

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {B : LinearMap.BilinForm ℝ L}

/-- On the plane of a `B`-orthonormal pair `(q, p)` with `⁅H, q⁆ = a p` and `⁅H, p⁆ = -a q`, the
map `ad H` is `a` times the quarter turn. -/
private theorem lie_eq_smul_quarterTurn {q p H v : L} {a : ℝ} (hqq : B q q = 1) (hqp : B q p = 0)
    (hpq : B p q = 0) (hpp : B p p = 1) (hq : ⁅H, q⁆ = a • p) (hp : ⁅H, p⁆ = -(a • q))
    (hv : v ∈ Submodule.span ℝ {q, p}) : ⁅H, v⁆ = a • quarterTurn B q p v := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hv
  rw [lie_add, lie_smul, lie_smul, hq, hp, map_add, map_smul, map_smul,
    quarterTurn_apply_left hqq hpq, quarterTurn_apply_right hqp hpp]
  module

variable [FiniteDimensional ℝ L]

/-- The centralizer of `t`, together with the planes spanned by the pairs `(q k, p k)`. -/
private def rootPlaneFamily (t : Submodule ℝ L) {r : ℕ} (q p : Fin r → L) (o : Option (Fin r)) :
    Submodule ℝ L :=
  o.elim (⨅ H : t, LinearMap.ker (LieAlgebra.ad ℝ L H)) fun k ↦ Submodule.span ℝ {q k, p k}

/-- The real normal form of `H ↦ ad H` on `L`, transported from Euclidean space: `B`-orthonormal
pairs `(q k, p k)` with `⁅H, q k⁆ = α_k(H) p k` and `⁅H, p k⁆ = -α_k(H) q k`, whose planes together
with the centralizer of `t` form a `B`-orthogonal direct sum decomposition of `L`. -/
private theorem exists_isInternal_rootPlaneFamily (hB : B.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) (hinv : B.lieInvariant L) {t : Submodule ℝ L}
    (ht : ∀ H ∈ t, ∀ H' ∈ t, ⁅H, H'⁆ = 0) :
    ∃ (r : ℕ) (q p : Fin r → L) (α : Fin r → Dual ℝ t),
      (∀ i j, B (Sum.elim q p i) (Sum.elim q p j) = if i = j then 1 else 0) ∧
      (∀ k (H : t), ⁅(H : L), q k⁆ = α k H • p k ∧ ⁅(H : L), p k⁆ = -(α k H • q k)) ∧
      (∀ k, α k ≠ 0) ∧ DirectSum.IsInternal (rootPlaneFamily t q p) ∧
      ∀ o o', o ≠ o' → ∀ v ∈ rootPlaneFamily t q p o, ∀ w ∈ rootPlaneFamily t q p o',
        B w v = 0 := by
  obtain ⟨e, he⟩ := LinearMap.BilinForm.exists_linearEquiv_euclideanSpace_apply_apply hB hpos
  -- Transport `H ↦ ad H` to Euclidean space through `e` and take its real normal form.
  let ρ : t →ₗ[ℝ] Module.End ℝ (EuclideanSpace ℝ (Fin (finrank ℝ L))) :=
    LinearMap.mk₂ ℝ (fun H x ↦ e.symm ⁅(H : L), e x⁆) (by simp [add_lie]) (by simp [smul_lie])
      (by simp) (by simp)
  have hρ (H : t) (x) : e (ρ H x) = ⁅(H : L), e x⁆ := by simp [ρ]
  have hskew (H : t) (x y) : ⟪ρ H x, y⟫ = -⟪x, ρ H y⟫ := by
    rw [← he, ← he, hρ, hρ, hinv]
  have hcomm (H H' : t) : Commute (ρ H) (ρ H') := LinearMap.ext fun x ↦ e.injective <| by
    simp only [mul_apply_eq_comp, hρ]
    rw [leibniz_lie, ht H H.property H' H'.property, zero_lie, zero_add]
  obtain ⟨r, q, p, α, hon, hact, hne, hker⟩ :=
    exists_orthonormal_apply_eq_smul_of_skew_of_linearMap ρ hskew hcomm
  -- The summands are the images under `e` of the summands of the normal form.
  have hGE (o : Option (Fin r)) :
      (planeFamily q p o).map (e : _ →ₗ[ℝ] L) = rootPlaneFamily t (e ∘ q) (e ∘ p) o := by
    rcases o with _ | k
    · ext x
      simp only [planeFamily, rootPlaneFamily, Option.elim_none, hker, Submodule.mem_map_equiv,
        Submodule.mem_iInf, LinearMap.mem_ker, LieAlgebra.ad_apply]
      refine forall_congr' fun H ↦ ?_
      rw [← e.injective.eq_iff, hρ, LinearEquiv.apply_symm_apply, map_zero]
    · simp [planeFamily, rootPlaneFamily, Submodule.map_span]
  refine ⟨r, e ∘ q, e ∘ p, α, fun i j ↦ ?_, fun k H ↦ ⟨?_, ?_⟩, hne, ?_,
    fun o o' hoo' v hv w hw ↦ ?_⟩
  · rw [← Sum.comp_elim, Function.comp_apply, Function.comp_apply, he]
    split_ifs with h
    · rw [h, real_inner_self_eq_norm_sq, hon.1 j, one_pow]
    · exact hon.2 h
  · rw [Function.comp_apply, Function.comp_apply, ← hρ, (hact k H).1, map_smul]
  · rw [Function.comp_apply, Function.comp_apply, ← hρ, (hact k H).2, map_smul, neg_smul]
  · -- The direct sum decomposition is transported from the normal form.
    have hG := isInternal_planeFamily hon
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hG ⊢
    have hFG : rootPlaneFamily t (e ∘ q) (e ∘ p) =
        fun o ↦ Submodule.orderIsoMapComap e (planeFamily q p o) :=
      funext fun o ↦ by rw [Submodule.orderIsoMapComap_apply, hGE]
    rw [hFG]
    exact ⟨(iSupIndep_map_orderIso_iff _).2 hG.1, by
      rw [← OrderIso.map_iSup, hG.2, OrderIso.map_top]⟩
  · -- Vectors in distinct summands are `B`-orthogonal.
    rw [← hGE, Submodule.mem_map_equiv] at hv hw
    rw [← e.apply_symm_apply v, ← e.apply_symm_apply w, he]
    exact (pairwise_isOrtho_planeFamily hon hoo').symm.inner_eq hw hv

/-- **Root-plane decomposition.** Let `B` be a symmetric positive definite invariant bilinear form
on a finite-dimensional real Lie algebra `L` and let `t` be a subspace whose elements commute. Then
`L` is the internal direct sum of the centralizer `𝔷(t) = ⋂_{H ∈ t} ker (ad H)` and finitely many
two-dimensional root planes `E_k` of `t` with nonzero roots `α_k`, on which `ad H = α_k(H) J_k`;
the planes are `B`-orthogonal to each other and to `𝔷(t)`. -/
theorem exists_isInternal_isRootPlane (hB : B.IsSymm) (hpos : ∀ x, x ≠ 0 → 0 < B x x)
    (hinv : B.lieInvariant L) {t : Submodule ℝ L} (ht : ∀ H ∈ t, ∀ H' ∈ t, ⁅H, H'⁆ = 0) :
    ∃ (r : ℕ) (α : Fin r → Dual ℝ t) (E : Fin r → Submodule ℝ L)
      (J : (k : Fin r) → Module.End ℝ (E k)),
      DirectSum.IsInternal (fun o : Option (Fin r) ↦
        o.elim (⨅ H : t, LinearMap.ker (LieAlgebra.ad ℝ L H)) E) ∧
      (∀ k, IsRootPlane B t (α k) (E k) (J k)) ∧ (∀ k, α k ≠ 0) ∧
      (∀ k, finrank ℝ (E k) = 2) ∧
      (∀ k, E k ≤ B.orthogonal (⨅ H : t, LinearMap.ker (LieAlgebra.ad ℝ L H))) ∧
      Pairwise fun k l ↦ E k ≤ B.orthogonal (E l) := by
  obtain ⟨r, q, p, α, hB', hact, hne, hint, horth⟩ :=
    exists_isInternal_rootPlaneFamily hB hpos hinv ht
  have hqq (k : Fin r) : B (q k) (q k) = 1 := by simpa using hB' (.inl k) (.inl k)
  have hqp (k : Fin r) : B (q k) (p k) = 0 := by simpa using hB' (.inl k) (.inr k)
  have hpq (k : Fin r) : B (p k) (q k) = 0 := by simpa using hB' (.inr k) (.inl k)
  have hpp (k : Fin r) : B (p k) (p k) = 1 := by simpa using hB' (.inr k) (.inr k)
  refine ⟨r, α, fun k ↦ Submodule.span ℝ {q k, p k}, fun k ↦ (quarterTurn B (q k) (p k)).restrict
    fun v _ ↦ quarterTurn_mem_span _ _ v, hint, fun k ↦ ⟨fun v ↦ ?_,
    fun v w ↦ apply_quarterTurn hB _ _ v w, fun H v ↦ ?_⟩, hne,
    fun k ↦ finrank_span_pair (hqq k) (hqp k) (hpq k) (hpp k),
    fun k v hv c hc ↦ horth (some k) none (by simp) v hv c hc,
    fun k l hkl v hv w hw ↦ horth (some k) (some l) (by simpa using hkl) v hv w hw⟩
  · exact Subtype.ext (quarterTurn_quarterTurn (hqq k) (hqp k) (hpq k) (hpp k) v.property)
  · exact lie_eq_smul_quarterTurn (hqq k) (hqp k) (hpq k) (hpp k) (hact k H).1 (hact k H).2
      v.property

end TauCeti
