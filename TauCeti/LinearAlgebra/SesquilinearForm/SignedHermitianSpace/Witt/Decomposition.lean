/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Hyperbolic

/-!
# Witt decomposition and the Witt index of a signed hermitian space

The **Witt index** of a signed hermitian space `(V, h)` over a commutative ring with involution is
the largest size of a hyperbolic frame of `V`, the largest `r` such that the hyperbolic space
`H^r` embeds isometrically in `V` (`TauCeti.SignedHermitianSpace.wittIndex`). It is an isometry
invariant, at most half the rank, and equal to `r` on `H^r`.

Over a field whose involution `σ` is not the identity, in every characteristic and for both
signs, this file proves **Witt's decomposition theorem**: a finite-dimensional signed hermitian
space is isometric to `H^r ⊥ V_an` with `V_an` anisotropic, where `r` is the Witt index and the
isometry class of `V_an` is unique (`TauCeti.SignedHermitianSpace.exists_equivalent_hyperbolic_prod`
and `TauCeti.SignedHermitianSpace.eq_and_equivalent_of_equivalent_hyperbolic_prod`). The Witt
index is also the largest dimension of a totally isotropic subspace, and it vanishes exactly on
the anisotropic spaces. A plane is hyperbolic as soon as it is isotropic; in particular
`⟨a, -a⟩ ≅ H`.

Existence: a hyperbolic frame of maximal size `r` splits off, `V ≅ H^r ⊥ Pᗮ`, and `Pᗮ` is
anisotropic, since an isotropic vector of `Pᗮ` would prolong the isotropic half of the frame to a
totally isotropic family of size `r + 1`, the first half of a larger hyperbolic frame. Uniqueness:
if `H^r ⊥ A ≅ H^s ⊥ B` with `r < s`, split `H^r` off the right side as well; Witt cancellation
then identifies `A` with a complement of `H^r` in `H^s ⊥ B`, which contains an isotropic vector of
`H^s`. For `r = s` it is cancellation itself
(`TauCeti.SignedHermitianSpace.equivalent_of_equivalent_prod`).

## Main definitions

* `TauCeti.SignedHermitianSpace.wittIndex`: the Witt index.

## Main statements

* `TauCeti.SignedHermitianSpace.two_mul_wittIndex_le_finrank`: `2 r ≤ dim V`.
* `TauCeti.SignedHermitianSpace.Equivalent.wittIndex_eq`: the Witt index is an isometry invariant.
* `TauCeti.SignedHermitianSpace.wittIndex_hyperbolic`: the Witt index of `H^ι` is `|ι|`.
* `TauCeti.SignedHermitianSpace.exists_equivalent_hyperbolic_prod`: **Witt decomposition**,
  existence.
* `TauCeti.SignedHermitianSpace.eq_and_equivalent_of_equivalent_hyperbolic_prod`: **Witt
  decomposition**, uniqueness of the number of hyperbolic planes and of the anisotropic part.
* `TauCeti.SignedHermitianSpace.wittIndex_eq_of_equivalent_hyperbolic_prod`: every Witt
  decomposition has `wittIndex` hyperbolic planes.
* `TauCeti.SignedHermitianSpace.wittIndex_hyperbolic_prod`: `wittIndex (H^r ⊥ V) = r + wittIndex V`.
* `TauCeti.SignedHermitianSpace.wittIndex_eq_zero_iff`: the Witt index vanishes exactly on
  anisotropic spaces.
* `TauCeti.SignedHermitianSpace.finrank_le_wittIndex`,
  `TauCeti.SignedHermitianSpace.exists_finrank_eq_wittIndex`: the Witt index is the largest
  dimension of a totally isotropic subspace.
* `TauCeti.SignedHermitianSpace.equivalent_hyperbolic_of_finrank_eq_two`: an isotropic plane is
  hyperbolic; `TauCeti.SignedHermitianSpace.equivalent_hyperbolic_diagonal`: `⟨a, -a⟩ ≅ H`.

## Attribution

The bound of a totally isotropic frame by the number of hyperbolic planes is, for
`U(p, q)` over a CM field, grh-lean's `New.Space.card_le_card_preimage_of_isotropic` and the
splitting `New.Space.exists_splitting` (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright
2026 Anthropic, PBC, file `src/Lib/Adelic/Witt/IwasawaDecomposition.lean`), proved there through
signatures and Landherr's theorem. The argument here is the classical one by Witt cancellation.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7, §2.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4, for the
  quadratic case.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

section CommRing

variable {K V V₁ V₂ : Type*} [CommRing K] {σ : K →+* K} {ε : ℤˣ} [AddCommGroup V] [Module K V]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  (H : SignedHermitianSpace K V σ ε)

/-- The **Witt index** of a signed hermitian space: the largest `k` for which `(V, h)` has a
hyperbolic frame of size `k`, equivalently an isometric embedding of the hyperbolic space `H^k`.
For a finite module over a nontrivial ring this is a maximum
(`TauCeti.SignedHermitianSpace.exists_isHyperbolicFrame_wittIndex`). For finite-dimensional `V`
over a field whose involution is not the identity, it is the largest dimension of a totally
isotropic subspace (`TauCeti.SignedHermitianSpace.finrank_le_wittIndex`,
`TauCeti.SignedHermitianSpace.exists_finrank_eq_wittIndex`). -/
noncomputable def wittIndex : ℕ :=
  sSup {k | ∃ x y : Fin k → V, H.IsHyperbolicFrame x y}

variable {H}

/-- The Witt index is an isometry invariant. -/
theorem Equivalent.wittIndex_eq {H₁ : SignedHermitianSpace K V₁ σ ε} (h : Equivalent H H₁) :
    H.wittIndex = H₁.wittIndex := by
  obtain ⟨e⟩ := h.nonempty
  unfold wittIndex
  congr 1
  ext k
  exact ⟨fun ⟨_, _, hxy⟩ ↦ ⟨_, _, hxy.map (f := e.toLinearEquiv.toLinearMap) e.map_app⟩,
    fun ⟨_, _, hxy⟩ ↦ ⟨_, _, hxy.map (f := e.symm.toLinearEquiv.toLinearMap) e.symm.map_app⟩⟩

variable (H) in
/-- There is a hyperbolic frame whose size is the Witt index. (When the sizes of hyperbolic
frames are unbounded, as for an infinite orthogonal sum of hyperbolic planes, the Witt index is
`0` by convention.) -/
theorem exists_isHyperbolicFrame_wittIndex :
    ∃ x y : Fin H.wittIndex → V, H.IsHyperbolicFrame x y := by
  by_cases hb : BddAbove {k | ∃ x y : Fin k → V, H.IsHyperbolicFrame x y}
  · exact Nat.sSup_mem (s := {k | ∃ x y : Fin k → V, H.IsHyperbolicFrame x y})
      ⟨0, Fin.elim0, Fin.elim0, ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩ hb
  · rw [wittIndex, Nat.sSup_of_not_bddAbove hb]
    exact ⟨Fin.elim0, Fin.elim0, ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩⟩

variable [Module.Finite K V]

/-- A hyperbolic frame of `V` has at most `dim V / 2` members. -/
theorem IsHyperbolicFrame.two_mul_card_le_finrank [Nontrivial K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {x y : ι → V} (hxy : H.IsHyperbolicFrame x y) :
    2 * Fintype.card ι ≤ finrank K V := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · simp
  have := hxy.ringHomInvPair i
  have := LinearMap.finrank_le_finrank_of_injective hxy.injective_hyperbolicFrameMap
  simpa [two_mul] using this

private theorem bddAbove_wittIndex [Nontrivial K] :
    BddAbove {k | ∃ x y : Fin k → V, H.IsHyperbolicFrame x y} :=
  ⟨finrank K V, fun k ⟨_, _, hxy⟩ ↦ by
    have := hxy.two_mul_card_le_finrank
    simp only [Fintype.card_fin] at this
    lia⟩

/-- The size of a hyperbolic frame is at most the Witt index. -/
theorem IsHyperbolicFrame.card_le_wittIndex [Nontrivial K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {x y : ι → V} (hxy : H.IsHyperbolicFrame x y) :
    Fintype.card ι ≤ H.wittIndex :=
  le_csSup bddAbove_wittIndex ⟨x ∘ (Fintype.equivFin ι).symm, y ∘ (Fintype.equivFin ι).symm,
    hxy.comp (Fintype.equivFin ι).symm.injective⟩

variable (H) in
/-- Twice the Witt index is at most the rank. -/
theorem two_mul_wittIndex_le_finrank : 2 * H.wittIndex ≤ finrank K V := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · -- Over the zero ring every family of zeros is a hyperbolic frame, so the Witt index is `0`.
    have hnb : ¬BddAbove {k | ∃ x y : Fin k → V, H.IsHyperbolicFrame x y} := fun ⟨m, hm⟩ ↦ by
      have := hm (show m + 1 ∈ {k | ∃ x y : Fin k → V, H.IsHyperbolicFrame x y} from
        ⟨0, 0, ⟨by simp, by simp, fun _ _ ↦ Subsingleton.elim _ _⟩⟩)
      lia
    rw [wittIndex, Nat.sSup_of_not_bddAbove hnb]
    simp
  · obtain ⟨x, y, hxy⟩ := H.exists_isHyperbolicFrame_wittIndex
    simpa using hxy.two_mul_card_le_finrank

/-- The Witt index of the hyperbolic space `H^ι` is the cardinality of `ι`. -/
theorem wittIndex_hyperbolic [RingHomInvPair σ σ] [Nontrivial K] (ι : Type*) [Fintype ι] :
    (hyperbolic K σ ε ι).wittIndex = Fintype.card ι := by
  classical
  refine le_antisymm ?_ isHyperbolicFrame_hyperbolic.card_le_wittIndex
  have := (hyperbolic K σ ε ι).two_mul_wittIndex_le_finrank
  simp only [finrank_prod, finrank_fintype_fun_eq_card] at this
  lia

/-- A hyperbolic summand raises the Witt index: `|ι| ≤ wittIndex (H^ι ⊥ V)`. -/
theorem card_le_wittIndex_hyperbolic_prod [RingHomInvPair σ σ] [Nontrivial K] (ι : Type*)
    [Fintype ι] (H₁ : SignedHermitianSpace K V₁ σ ε) [Module.Finite K V₁] :
    Fintype.card ι ≤ ((hyperbolic K σ ε ι).prod H₁).wittIndex := by
  classical
  exact (isHyperbolicFrame_hyperbolic_prod H₁).card_le_wittIndex

end CommRing

section Field

variable {K V V₁ V₂ : Type*} [Field K] {σ : K →+* K} [RingHomInvPair σ σ] {ε : ℤˣ}
  [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  {H : SignedHermitianSpace K V σ ε}

omit [RingHomInvPair σ σ] in
/-- A frame `x, y` and a vector `z` orthogonal to its span: `Fin.snoc x z` is totally isotropic
when `h z z = 0`. -/
private theorem form_snoc_eq_zero {k : ℕ} {x y : Fin k → V} (hxy : H.IsHyperbolicFrame x y)
    {z : V} (hz : z ∈ (LinearMap.range (hyperbolicFrameMap K x y)).orthogonalBilin H.form)
    (hzz : H.form z z = 0) (i j : Fin (k + 1)) :
    H.form ((Fin.snoc x z : Fin (k + 1) → V) i) ((Fin.snoc x z : Fin (k + 1) → V) j) = 0 := by
  have hxz (i : Fin k) : H.form (x i) z = 0 := (Submodule.mem_orthogonalBilin.1 hz) _
    ⟨(Pi.single i 1, 0), by simp [hyperbolicFrameMap_apply, Pi.single_apply]⟩
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [hzz, hxz, H.isRefl _ _ (hxz _), hxy.form_left]

/-- **The complement of a maximal hyperbolic frame is anisotropic.** If `x, y` is a hyperbolic
frame whose size is the Witt index of a finite-dimensional space, then the orthogonal of its span
is anisotropic. -/
theorem IsHyperbolicFrame.anisotropic_restrict_orthogonalBilin [FiniteDimensional K V]
    (hσ : ∃ z, σ z ≠ z) {x y : Fin H.wittIndex → V} (hxy : H.IsHyperbolicFrame x y) :
    (H.restrict _ (H.separatingLeft_domRestrict_orthogonalBilin
      hxy.separatingLeft_domRestrict_range)).Anisotropic := by
  rw [anisotropic_iff]
  rintro ⟨z, hz⟩ hiso
  obtain ⟨hzz, hz₀⟩ := isIsotropic_iff.1 hiso
  replace hz₀ : z ≠ 0 := fun h ↦ hz₀ (Subtype.ext h)
  -- `z` is not in the span of `x`, which lies in the span `P` of the frame, as `P ⊓ Pᗮ = 0`.
  have hzx : z ∉ Submodule.span K (Set.range x) := fun hzx ↦ hz₀ <|
    (Submodule.disjoint_def.1 ((H.separatingLeft_domRestrict_iff _).1
      hxy.separatingLeft_domRestrict_range)) z
      (by rw [range_hyperbolicFrameMap]; exact Submodule.mem_sup_left hzx) hz
  obtain ⟨y', hy'⟩ := exists_isHyperbolicFrame hσ (hxy.linearIndependent_left.finSnoc hzx)
    (form_snoc_eq_zero hxy hz (by rwa [restrict_form_apply] at hzz))
  have := hy'.card_le_wittIndex
  simp at this

/-- **Witt decomposition**, existence. Over a field whose involution is not the identity, a
finite-dimensional signed hermitian space is isometric to the orthogonal sum of `wittIndex`
hyperbolic planes and an anisotropic space. -/
theorem exists_equivalent_hyperbolic_prod [FiniteDimensional K V] (hσ : ∃ z, σ z ≠ z) :
    ∃ (W : Submodule K V) (hW : (H.form.domRestrict₁₂ W W).SeparatingLeft),
      (H.restrict W hW).Anisotropic ∧
        Equivalent H ((hyperbolic K σ ε (Fin H.wittIndex)).prod (H.restrict W hW)) := by
  obtain ⟨x, y, hxy⟩ := H.exists_isHyperbolicFrame_wittIndex
  exact ⟨_, _, hxy.anisotropic_restrict_orthogonalBilin hσ, hxy.equivalent_hyperbolic_prod⟩

/-- `H^s ⊥ B` with `r < s` is the orthogonal sum of `H^r` and a space that is not anisotropic. -/
private theorem not_equivalent_hyperbolic_prod_of_lt (hσ : ∃ z, σ z ≠ z) {r s : ℕ} (hrs : r < s)
    {A : SignedHermitianSpace K V₁ σ ε} (B : SignedHermitianSpace K V₂ σ ε) (hA : A.Anisotropic) :
    ¬Equivalent ((hyperbolic K σ ε (Fin r)).prod A) ((hyperbolic K σ ε (Fin s)).prod B) := by
  intro h
  -- The standard frame of `H^s`, in `H^s ⊥ B`, and its first `r` pairs.
  have hfull := isHyperbolicFrame_hyperbolic_prod (ι := Fin s) (σ := σ) (ε := ε) B
  have hxy := hfull.comp (Fin.castLE_injective hrs.le)
  have hC := (equivalent_of_equivalent_prod hσ
    (h.trans hxy.equivalent_hyperbolic_prod)).anisotropic_iff.1 hA
  -- The `r`-th standard isotropic vector of `H^s` is orthogonal to the first `r` pairs.
  rw [anisotropic_iff] at hC
  refine hC ⟨((Pi.single ⟨r, hrs⟩ 1, 0), 0), ?_⟩ (isIsotropic_iff.2 ⟨?_, ?_⟩)
  · rw [range_hyperbolicFrameMap, Submodule.orthogonalBilin_sup]
    refine ⟨Submodule.mem_orthogonalBilin_span.2 ?_, Submodule.mem_orthogonalBilin_span.2 ?_⟩ <;>
      rintro _ ⟨i, rfl⟩
    · exact hfull.form_left _ ⟨r, hrs⟩
    · refine (hfull.form_right_left _ ⟨r, hrs⟩).trans (ite_eq_right_iff.2 fun hi ↦ ?_)
      exact absurd (by simpa [Fin.ext_iff] using hi) (Fin.is_lt i).ne
  · rw [restrict_form_apply]
    exact hfull.form_left ⟨r, hrs⟩ ⟨r, hrs⟩
  · intro h0
    have h1 := congrArg (fun v ↦ v.1.1 ⟨r, hrs⟩) (congrArg Subtype.val h0)
    simp at h1

/-- **Witt decomposition**, uniqueness. Over a field whose involution is not the identity, if
`H^r ⊥ A ≅ H^s ⊥ B` with `A` and `B` anisotropic, then `r = s` and `A ≅ B`. -/
theorem eq_and_equivalent_of_equivalent_hyperbolic_prod (hσ : ∃ z, σ z ≠ z) {r s : ℕ}
    {A : SignedHermitianSpace K V₁ σ ε} {B : SignedHermitianSpace K V₂ σ ε} (hA : A.Anisotropic)
    (hB : B.Anisotropic)
    (h : Equivalent ((hyperbolic K σ ε (Fin r)).prod A) ((hyperbolic K σ ε (Fin s)).prod B)) :
    r = s ∧ Equivalent A B := by
  rcases lt_trichotomy r s with hrs | rfl | hrs
  · exact (not_equivalent_hyperbolic_prod_of_lt hσ hrs B hA h).elim
  · exact ⟨rfl, equivalent_of_equivalent_prod hσ h⟩
  · exact (not_equivalent_hyperbolic_prod_of_lt hσ hrs A hB h.symm).elim

/-- Every Witt decomposition `V ≅ H^r ⊥ A`, `A` anisotropic, has `r = wittIndex V`: the
hyperbolic frames of `V` have at most `r` members. The space need not be finite-dimensional. -/
theorem wittIndex_eq_of_equivalent_hyperbolic_prod (hσ : ∃ z, σ z ≠ z) {r : ℕ}
    {A : SignedHermitianSpace K V₁ σ ε} (hA : A.Anisotropic)
    (h : Equivalent H ((hyperbolic K σ ε (Fin r)).prod A)) : H.wittIndex = r := by
  obtain ⟨e⟩ := h.symm.nonempty
  refine IsGreatest.csSup_eq ⟨⟨_, _, (isHyperbolicFrame_hyperbolic_prod A).map
    (f := e.toLinearEquiv.toLinearMap) e.map_app⟩, ?_⟩
  rintro k ⟨x, y, hxy⟩
  by_contra hk
  exact not_equivalent_hyperbolic_prod_of_lt hσ (not_le.1 hk) _ hA
    (h.symm.trans hxy.equivalent_hyperbolic_prod)

/-- **Adjoining hyperbolic planes raises the Witt index**: over a field whose involution is not
the identity, `wittIndex (H^r ⊥ V) = r + wittIndex V` for finite-dimensional `V`. -/
theorem wittIndex_hyperbolic_prod [FiniteDimensional K V₁] (hσ : ∃ z, σ z ≠ z) (r : ℕ)
    (H₁ : SignedHermitianSpace K V₁ σ ε) :
    ((hyperbolic K σ ε (Fin r)).prod H₁).wittIndex = r + H₁.wittIndex := by
  obtain ⟨W, hW, hWa, hHW⟩ := exists_equivalent_hyperbolic_prod (H := H₁) hσ
  -- `H^r ⊥ V ≅ H^r ⊥ (H^s ⊥ A) ≅ (H^r ⊥ H^s) ⊥ A ≅ H^(r + s) ⊥ A`.
  refine wittIndex_eq_of_equivalent_hyperbolic_prod hσ hWa (((Equivalent.refl _).prod hHW).trans
    ((IsometryEquiv.prodAssoc _ _ _).symm.equivalent.trans (Equivalent.prod ?_ (.refl _))))
  exact ((IsometryEquiv.hyperbolicSum _ _).symm.trans
    (IsometryEquiv.hyperbolicCongr finSumFinEquiv)).equivalent

/-- Over a field whose involution is not the identity, a finite-dimensional signed hermitian
space has Witt index zero exactly when it is anisotropic. -/
theorem wittIndex_eq_zero_iff [FiniteDimensional K V] (hσ : ∃ z, σ z ≠ z) :
    H.wittIndex = 0 ↔ H.Anisotropic := by
  rw [anisotropic_iff]
  refine ⟨fun h x hx ↦ ?_, fun h ↦ Nat.eq_zero_of_not_pos fun hpos ↦ ?_⟩
  · obtain ⟨y, hy⟩ := hx.exists_isHyperbolicFrame hσ
    have := hy.card_le_wittIndex
    simp [h] at this
  · obtain ⟨x, y, hxy⟩ := H.exists_isHyperbolicFrame_wittIndex
    exact h _ (hxy.isIsotropic_left ⟨0, hpos⟩)

/-- A totally isotropic subspace has dimension at most the Witt index. -/
theorem finrank_le_wittIndex [FiniteDimensional K V] (hσ : ∃ z, σ z ≠ z) {U : Submodule K V}
    (hU : ∀ x ∈ U, ∀ y ∈ U, H.form x y = 0) : finrank K U ≤ H.wittIndex := by
  let b := Module.finBasis K U
  obtain ⟨y, hy⟩ := exists_isHyperbolicFrame (H := H) hσ (x := fun i ↦ (b i : V))
    (b.linearIndependent.map' U.subtype U.ker_subtype)
    fun i j ↦ hU _ (b i).property _ (b j).property
  simpa using hy.card_le_wittIndex

/-- Some totally isotropic subspace has dimension the Witt index. -/
theorem exists_finrank_eq_wittIndex :
    ∃ U : Submodule K V, (∀ x ∈ U, ∀ y ∈ U, H.form x y = 0) ∧ finrank K U = H.wittIndex := by
  obtain ⟨x, y, hxy⟩ := H.exists_isHyperbolicFrame_wittIndex
  refine ⟨Submodule.span K (Set.range x), fun u hu v hv ↦ ?_, by
    simpa using finrank_span_eq_card hxy.linearIndependent_left⟩
  have : Submodule.span K (Set.range x) ≤ (Submodule.span K (Set.range x)).orthogonalBilin H.form :=
    Submodule.span_le.2 fun _ ⟨j, hj⟩ ↦ hj ▸ Submodule.mem_orthogonalBilin_span.2
      fun _ ⟨i, hi⟩ ↦ hi ▸ hxy.form_left i j
  exact Submodule.mem_orthogonalBilin.1 (this hv) u hu

/-- A hyperbolic frame of size half the dimension identifies the space with a hyperbolic space. -/
theorem IsHyperbolicFrame.equivalent_hyperbolic [FiniteDimensional K V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {x y : ι → V} (hxy : H.IsHyperbolicFrame x y)
    (h : 2 * Fintype.card ι = finrank K V) :
    Equivalent (SignedHermitianSpace.hyperbolic K σ ε ι) H :=
  IsometryEquiv.equivalent
    { LinearMap.linearEquivOfInjective _ hxy.injective_hyperbolicFrameMap (by simp [← h, two_mul])
      with
      map_app' := fun u v ↦ by
        simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
          LinearMap.linearEquivOfInjective_apply, hxy.form_hyperbolicFrameMap] }

/-- **Isotropic planes are hyperbolic.** Over a field whose involution is not the identity, a
two-dimensional signed hermitian space with an isotropic vector is isometric to the hyperbolic
plane. -/
theorem equivalent_hyperbolic_of_finrank_eq_two (hσ : ∃ z, σ z ≠ z) (hV : finrank K V = 2)
    (h : ¬H.Anisotropic) : Equivalent (hyperbolic K σ ε (Fin 1)) H := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  obtain ⟨x, hx⟩ := not_forall_not.1 (by rwa [anisotropic_iff] at h)
  obtain ⟨y, hy⟩ := hx.exists_isHyperbolicFrame hσ
  exact hy.equivalent_hyperbolic (by simp [hV])

/-- **`⟨a, -a⟩` is the hyperbolic plane.** Over a field whose involution is not the identity, for
every nonzero `a` with `σ a = ε • a` the diagonal plane `⟨a, -a⟩` is hyperbolic. -/
theorem equivalent_hyperbolic_diagonal (hσ : ∃ z, σ z ≠ z) {a : K} (ha : σ a = ε • a)
    (ha₀ : a ≠ 0) :
    Equivalent (hyperbolic K σ ε (Fin 1)) (diagonal σ ε ![a, -a]
      (fun i ↦ by fin_cases i <;> simp [ha])
      (fun i ↦ by fin_cases i <;> simp [ha₀])) := by
  refine equivalent_hyperbolic_of_finrank_eq_two hσ (by simp) fun h ↦
    (anisotropic_iff.1 h) ![1, 1] ?_
  refine isIsotropic_iff.2 ⟨by simp [Fin.sum_univ_two], fun h₁ ↦ ?_⟩
  simpa using congrFun h₁ 0

end Field

end SignedHermitianSpace

end TauCeti
