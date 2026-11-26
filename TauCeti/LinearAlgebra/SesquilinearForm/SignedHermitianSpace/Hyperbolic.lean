/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Orthogonal
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Witt

/-!
# Hyperbolic spaces, isotropic vectors and hyperbolic frames

Let `K` be a commutative ring with an involution `σ` and `ε = ±1`. The **hyperbolic space**
`H^ι` is `(ι → K) × (ι → K)` with the `ε`-hermitian form
`h ((a, b), (c, d)) = ∑ σ (aᵢ) dᵢ + ε σ (bᵢ) cᵢ`, whose Gram matrix in the standard basis is
`[[0, 1], [ε, 0]]` in blocks; for `ι` with one element it is the **hyperbolic plane** `H`. The
**diagonal space** `⟨a₁, …, aₙ⟩` is `Kⁿ` with the form `∑ σ (xᵢ) aᵢ yᵢ`.

A vector `x` of a signed hermitian space is **isotropic** if `h x x = 0` and `K x` is free of
rank one, that is `c • x = 0` only for `c = 0`; over a field this says `x ≠ 0`, while over the
split algebra `F × F` it excludes the vectors with a zero component, which lie in no hyperbolic
plane. A space is **anisotropic** if it has no isotropic vector. A **hyperbolic frame** of
`(V, h)` is a pair of families `xᵢ`, `yᵢ` with `h xᵢ xⱼ = h yᵢ yⱼ = 0` and `h xᵢ yⱼ = δᵢⱼ`:
equivalently, an isometric linear map `H^ι → V` (`TauCeti.SignedHermitianSpace.hyperbolicFrameMap`),
necessarily injective.

Over a field whose involution is not the identity, every linearly independent family spanning a
totally isotropic subspace is the first half of a hyperbolic frame
(`TauCeti.SignedHermitianSpace.exists_isHyperbolicFrame`); in particular every isotropic vector
lies in a hyperbolic plane. The span of a hyperbolic frame is nondegenerate, so it splits off:
`V ≅ H^ι ⊥ Pᗮ` (`TauCeti.SignedHermitianSpace.IsHyperbolicFrame.equivalent_hyperbolic_prod`).

The dual vectors `yⱼ` are first chosen with `h xᵢ yⱼ = δᵢⱼ`, which nondegeneracy allows; then
`yⱼ` is corrected by a combination of the `xᵢ` to make the `yⱼ` mutually orthogonal and isotropic.
For `i < j` the correction kills `h yᵢ yⱼ` directly, and for `i = j` it uses that every
`c` with `σ c = ε c` is `s + ε σ s` (`TauCeti.exists_units_add_smul_eq`); this is where the
nontrivial involution replaces division by `2`.

## Main definitions

* `TauCeti.SignedHermitianSpace.diagonal σ ε a`: the diagonal space `⟨a₁, …, aₙ⟩`.
* `TauCeti.SignedHermitianSpace.hyperbolic K σ ε ι`: the hyperbolic space `H^ι`.
* `TauCeti.SignedHermitianSpace.IsIsotropic`, `TauCeti.SignedHermitianSpace.Anisotropic`.
* `TauCeti.SignedHermitianSpace.IsHyperbolicFrame`: hyperbolic frames, and
  `TauCeti.SignedHermitianSpace.hyperbolicFrameMap`, the map `H^ι → V` of a frame.
* `TauCeti.SignedHermitianSpace.IsometryEquiv.hyperbolicSum`: `H^(ι ⊕ κ) ≅ H^ι ⊥ H^κ`, and
  `TauCeti.SignedHermitianSpace.IsometryEquiv.hyperbolicCongr`: reindexing.

## Main statements

* `TauCeti.SignedHermitianSpace.isIsotropic_iff`: over a field, `x` is isotropic exactly when
  `h x x = 0` and `x ≠ 0`.
* `TauCeti.SignedHermitianSpace.IsHyperbolicFrame.form_hyperbolicFrameMap`: a hyperbolic frame is
  an isometric map from `H^ι`.
* `TauCeti.SignedHermitianSpace.exists_isHyperbolicFrame`: a linearly independent totally
  isotropic family extends to a hyperbolic frame.
* `TauCeti.SignedHermitianSpace.exists_form_eq_zero_form_eq_one`: every isotropic vector lies in
  a hyperbolic plane.
* `TauCeti.SignedHermitianSpace.IsHyperbolicFrame.equivalent_hyperbolic_prod`: a hyperbolic frame
  splits off as an orthogonal summand.

## Attribution

The extension of an isotropic frame to a pair of dual isotropic frames, and the splitting of `V`
along it, follow grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic, PBC), file `src/Lib/Adelic/Witt/IwasawaDecomposition.lean`:
`New.Space.exists_splitting_of_perp_eq`, which corrects a dual frame `e` to `e - ½ k (eᴴ J e)`
over a CM field. Here the correction is triangular, so that it works in every characteristic, and
the statements are for signed hermitian spaces of either sign over any field with a nontrivial
involution; the splitting goes through orthogonal complements
(`TauCeti/LinearAlgebra/SesquilinearForm/SignedHermitianSpace/Orthogonal.lean`).

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7, §2.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

section CommRing

variable {K V V₁ V₂ : Type*} [CommRing K] {σ : K →+* K} {ε : ℤˣ} [AddCommGroup V] [Module K V]
  [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

/-! ### Diagonal and hyperbolic spaces -/

section Spaces

variable [RingHomInvPair σ σ]

variable (σ ε) in
/-- The **diagonal space** `⟨a₁, …, aₙ⟩`: the module `n → K` with the form
`h x y = ∑ σ (x i) * a i * y i`, for non-zero-divisors `a i` with `σ (a i) = ε • a i`. -/
def diagonal {n : Type*} [Fintype n] (a : n → K) (ha : ∀ i, σ (a i) = ε • a i)
    (ha₀ : ∀ i, a i ∈ nonZeroDivisors K) : SignedHermitianSpace K (n → K) σ ε where
  form := LinearMap.mk₂'ₛₗ σ (RingHom.id K) (fun x y ↦ ∑ i, σ (x i) * a i * y i)
    (fun _ _ _ ↦ by simp [add_mul, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by simp [Finset.mul_sum, mul_assoc])
    (fun _ _ _ ↦ by simp [mul_add, Finset.sum_add_distrib])
    (fun _ _ _ ↦ by
      simp only [smul_eq_mul, Pi.smul_apply, Finset.mul_sum, RingHom.id_apply]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring)
  form_swap x y := by
    simp only [LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, ha, RingHomInvPair.comp_apply_eq₂,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hε : ((ε : ℤ) : K) ^ 2 = 1 := by rw [← Int.cast_pow, Int.isUnit_sq ε.isUnit, Int.cast_one]
    rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul]
    linear_combination (-(σ (y i) * a i * x i)) * hε
  separatingLeft x hx := funext fun j ↦ by
    classical
    have hj : σ (x j) * a j = 0 := by simpa [Pi.single_apply] using hx (Pi.single j 1)
    have := (mul_right_mem_nonZeroDivisors_eq_zero_iff (ha₀ j)).1 hj
    rw [Pi.zero_apply, ← RingHomInvPair.comp_apply_eq₂ (σ := σ) (σ' := σ) (x := x j), this,
      map_zero]

/-- The form of `⟨a₁, …, aₙ⟩` is `∑ σ (x i) * a i * y i`. -/
@[simp]
theorem diagonal_form_apply {n : Type*} [Fintype n] (a : n → K) (ha : ∀ i, σ (a i) = ε • a i)
    (ha₀ : ∀ i, a i ∈ nonZeroDivisors K) (x y : n → K) :
    (diagonal σ ε a ha ha₀).form x y = ∑ i, σ (x i) * a i * y i :=
  (rfl)

variable (K σ ε) in
/-- The **hyperbolic space** `H^ι`: the module `(ι → K) × (ι → K)` with the form
`h ((a, b), (c, d)) = ∑ i, (σ (a i) * d i + ε • (σ (b i) * c i))`. The two factors are totally
isotropic and paired by `h`; for `ι` with one element this is the **hyperbolic plane**, with Gram
matrix `[[0, 1], [ε, 0]]`. -/
def hyperbolic (ι : Type*) [Fintype ι] : SignedHermitianSpace K ((ι → K) × (ι → K)) σ ε where
  form := LinearMap.mk₂'ₛₗ σ (RingHom.id K)
    (fun x y ↦ ∑ i, (σ (x.1 i) * y.2 i + ε • (σ (x.2 i) * y.1 i)))
    (fun _ _ _ ↦ by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, add_mul, smul_add,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by abel)
    (fun _ _ _ ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul,
        Finset.mul_sum, mul_add, mul_smul_comm, mul_assoc])
    (fun _ _ _ ↦ by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, smul_add,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by abel)
    (fun c _ _ ↦ by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        Finset.mul_sum, mul_add, mul_smul_comm]
      exact Finset.sum_congr rfl fun _ _ ↦ by rw [mul_left_comm c, mul_left_comm c])
  form_swap x y := by
    simp only [LinearMap.mk₂'ₛₗ_apply, map_sum, map_add, map_mul, map_zsmul_unit,
      RingHomInvPair.comp_apply_eq₂, Finset.smul_sum, smul_add, smul_smul, Int.units_mul_self,
      one_smul]
    exact Finset.sum_congr rfl fun _ _ ↦ by rw [add_comm, mul_comm (σ _), mul_comm (σ _)]
  separatingLeft x hx := by
    classical
    have hσ (c : K) (hc : σ c = 0) : c = 0 := by
      rw [← RingHomInvPair.comp_apply_eq₂ (σ := σ) (σ' := σ) (x := c), hc, map_zero]
    refine Prod.ext (funext fun j ↦ hσ _ ?_) (funext fun j ↦ hσ _ ?_)
    · simpa [Pi.single_apply] using hx (0, Pi.single j 1)
    · have h := hx (Pi.single j 1, 0)
      simp [Pi.single_apply] at h
      simpa [smul_smul] using congrArg (ε • ·) h

/-- The form of `H^ι` is `∑ i, (σ (a i) * d i + ε • (σ (b i) * c i))`. -/
@[simp]
theorem hyperbolic_form_apply (ι : Type*) [Fintype ι] (x y : (ι → K) × (ι → K)) :
    (hyperbolic K σ ε ι).form x y = ∑ i, (σ (x.1 i) * y.2 i + ε • (σ (x.2 i) * y.1 i)) :=
  (rfl)

/-- The hyperbolic space of a sum of index types is the orthogonal sum of the hyperbolic spaces:
`H^(ι ⊕ κ) ≅ H^ι ⊥ H^κ`. -/
def IsometryEquiv.hyperbolicSum (ι κ : Type*) [Fintype ι] [Fintype κ] :
    IsometryEquiv (hyperbolic K σ ε (ι ⊕ κ)) ((hyperbolic K σ ε ι).prod (hyperbolic K σ ε κ)) :=
  { ((LinearEquiv.sumArrowLequivProdArrow ι κ K K).prodCongr
      (LinearEquiv.sumArrowLequivProdArrow ι κ K K)).trans
      (LinearEquiv.prodProdProdComm K _ _ _ _) with
    map_app' := fun x y ↦ by simp [Fintype.sum_sum_type] }

/-- Reindexing the hyperbolic space along `e : ι ≃ κ` is an isometry `H^ι ≅ H^κ`. -/
def IsometryEquiv.hyperbolicCongr {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    IsometryEquiv (hyperbolic K σ ε ι) (hyperbolic K σ ε κ) :=
  { (LinearEquiv.funCongrLeft K K e.symm).prodCongr (LinearEquiv.funCongrLeft K K e.symm) with
    map_app' := fun x y ↦ by
      simp only [hyperbolic_form_apply]
      exact e.symm.sum_comp (fun i ↦ σ (x.1 i) * y.2 i + ε • (σ (x.2 i) * y.1 i)) }

end Spaces

/-! ### Isotropic vectors -/

variable (H : SignedHermitianSpace K V σ ε)

/-- A vector `x` of a signed hermitian space is **isotropic** if `h x x = 0` and the submodule
`K x` is free of rank one: `c • x = 0` only for `c = 0`. Over a field the second condition says
`x ≠ 0` (`TauCeti.SignedHermitianSpace.isIsotropic_iff`). -/
@[expose] def IsIsotropic (x : V) : Prop :=
  H.form x x = 0 ∧ ∀ c : K, c • x = 0 → c = 0

/-- A signed hermitian space is **anisotropic** if it has no isotropic vector. -/
@[expose] def Anisotropic : Prop :=
  ∀ x, ¬H.IsIsotropic x

variable {H}

/-- Unfolding `Anisotropic`. -/
theorem anisotropic_iff : H.Anisotropic ↔ ∀ x, ¬H.IsIsotropic x :=
  Iff.rfl

/-- An isometric equivalence carries isotropic vectors to isotropic vectors. -/
theorem IsometryEquiv.isIsotropic_apply_iff {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} (e : IsometryEquiv H₁ H₂) {x : V₁} :
    H₂.IsIsotropic (e x) ↔ H₁.IsIsotropic x := by
  simp only [IsIsotropic, e.map_app, ← map_smul, map_eq_zero_iff e (EquivLike.injective e)]

/-- Anisotropy is invariant under isometry. -/
theorem Equivalent.anisotropic_iff {H₁ : SignedHermitianSpace K V₁ σ ε}
    {H₂ : SignedHermitianSpace K V₂ σ ε} (h : Equivalent H₁ H₂) :
    H₁.Anisotropic ↔ H₂.Anisotropic := by
  obtain ⟨e⟩ := h.nonempty
  refine ⟨fun h₁ y hy ↦ h₁ (e.symm y) ?_, fun h₂ x hx ↦ h₂ (e x) (e.isIsotropic_apply_iff.2 hx)⟩
  rwa [← e.isIsotropic_apply_iff, e.apply_symm_apply]

/-- An orthogonal sum with a space containing an isotropic vector is not anisotropic. -/
theorem not_anisotropic_prod {H₁ : SignedHermitianSpace K V₁ σ ε}
    (H₂ : SignedHermitianSpace K V₂ σ ε) {x : V₁} (hx : H₁.IsIsotropic x) :
    ¬(H₁.prod H₂).Anisotropic := fun h ↦
  h (x, 0) ⟨by simpa using hx.1, fun c hc ↦ hx.2 c (by simpa using congrArg Prod.fst hc)⟩

/-! ### Hyperbolic frames -/

variable (H) in
/-- A **hyperbolic frame** of a signed hermitian space, indexed by `ι`: two families `x`, `y`
with `h (x i) (x j) = 0`, `h (y i) (y j) = 0` and `h (x i) (y j) = δᵢⱼ`. For `ι` with one element
this is a hyperbolic pair, a basis of a hyperbolic plane. -/
structure IsHyperbolicFrame {ι : Type*} [DecidableEq ι] (x y : ι → V) : Prop where
  form_left : ∀ i j, H.form (x i) (x j) = 0
  form_right : ∀ i j, H.form (y i) (y j) = 0
  form_left_right : ∀ i j, H.form (x i) (y j) = if i = j then 1 else 0

variable (K) in
/-- The linear map `H^ι → V` of a pair of families `x`, `y`: `(a, b) ↦ ∑ aᵢ xᵢ + ∑ bᵢ yᵢ`. It is
isometric for a hyperbolic frame
(`TauCeti.SignedHermitianSpace.IsHyperbolicFrame.form_hyperbolicFrameMap`). -/
def hyperbolicFrameMap {ι : Type*} [Fintype ι] (x y : ι → V) : (ι → K) × (ι → K) →ₗ[K] V :=
  (Fintype.linearCombination K x).coprod (Fintype.linearCombination K y)

variable (K) in
/-- The map of a pair of families sends `(a, b)` to `∑ aᵢ xᵢ + ∑ bᵢ yᵢ`. -/
theorem hyperbolicFrameMap_apply {ι : Type*} [Fintype ι] (x y : ι → V) (u : (ι → K) × (ι → K)) :
    hyperbolicFrameMap K x y u = ∑ i, u.1 i • x i + ∑ i, u.2 i • y i := by
  simp [hyperbolicFrameMap, Fintype.linearCombination_apply]

variable (K) in
/-- The range of `hyperbolicFrameMap K x y` is the span of the two families. -/
theorem range_hyperbolicFrameMap {ι : Type*} [Fintype ι] (x y : ι → V) :
    LinearMap.range (hyperbolicFrameMap K x y) =
      Submodule.span K (Set.range x) ⊔ Submodule.span K (Set.range y) := by
  rw [hyperbolicFrameMap, LinearMap.range_coprod, Fintype.range_linearCombination,
    Fintype.range_linearCombination]

/-- The standard hyperbolic frame of `H^ι`: the vectors `(eᵢ, 0)` and `(0, eᵢ)`. -/
theorem isHyperbolicFrame_hyperbolic [RingHomInvPair σ σ] {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    (hyperbolic K σ ε ι).IsHyperbolicFrame (fun i ↦ (Pi.single i 1, 0))
      (fun i ↦ (0, Pi.single i 1)) where
  form_left i j := by simp
  form_right i j := by simp
  form_left_right i j := by simp [Pi.single_apply, eq_comm]

namespace IsHyperbolicFrame

variable {ι : Type*} [DecidableEq ι] {x y : ι → V}

/-- In a hyperbolic frame, `h (y i) (x j) = ε δᵢⱼ`. -/
theorem form_right_left (hxy : H.IsHyperbolicFrame x y) (i j : ι) :
    H.form (y i) (x j) = if i = j then ((ε : ℤ) : K) else 0 := by
  rw [H.form_swap, hxy.form_left_right, Units.smul_def, zsmul_eq_mul]
  split_ifs with h₁ h₂ h₂ <;> simp_all [eq_comm]

/-- An isometric linear map carries hyperbolic frames to hyperbolic frames. -/
theorem map {H₂ : SignedHermitianSpace K V₂ σ ε} (hxy : H.IsHyperbolicFrame x y)
    {f : V →ₗ[K] V₂} (hf : ∀ v w, H₂.form (f v) (f w) = H.form v w) :
    H₂.IsHyperbolicFrame (f ∘ x) (f ∘ y) where
  form_left i j := by simp [hf, hxy.form_left]
  form_right i j := by simp [hf, hxy.form_right]
  form_left_right i j := by simp [hf, hxy.form_left_right]

/-- Restricting a hyperbolic frame along an injective map of index types gives a hyperbolic
frame. -/
theorem comp {κ : Type*} [DecidableEq κ] (hxy : H.IsHyperbolicFrame x y) {e : κ → ι}
    (he : Function.Injective e) : H.IsHyperbolicFrame (x ∘ e) (y ∘ e) where
  form_left i j := hxy.form_left _ _
  form_right i j := hxy.form_right _ _
  form_left_right i j := by simp [hxy.form_left_right, he.eq_iff]

/-- A nonempty hyperbolic frame forces `σ` to be an involution: `h (x i) (c • y i) = c`, and
applying `ε`-hermitian symmetry twice gives `σ (σ c) = c`. -/
theorem ringHomInvPair (hxy : H.IsHyperbolicFrame x y) (i : ι) : RingHomInvPair σ σ := by
  have h (c : K) : σ (σ c) = c := by
    have h₁ : H.form (x i) (c • y i) = c := by simp [hxy.form_left_right]
    have h₂ := H.form_swap (c • y i) (x i)
    rw [H.form_swap (x i) (c • y i), h₁, map_zsmul_unit, smul_smul, Int.units_mul_self,
      one_smul] at h₂
    exact h₂.symm
  exact ⟨RingHom.ext h, RingHom.ext h⟩

/-- The vectors of a hyperbolic frame are isotropic. -/
theorem isIsotropic_left [RingHomInvPair σ σ] (hxy : H.IsHyperbolicFrame x y) (i : ι) :
    H.IsIsotropic (x i) := by
  refine ⟨hxy.form_left i i, fun c hc ↦ ?_⟩
  have h := congrArg (fun v ↦ H.form v (y i)) hc
  simp only [map_smulₛₗ, LinearMap.smul_apply, hxy.form_left_right, smul_eq_mul, map_zero,
    LinearMap.zero_apply, ↓reduceIte, mul_one] at h
  rw [← RingHomInvPair.comp_apply_eq₂ (σ := σ) (σ' := σ) (x := c), h, map_zero]

/-- A hyperbolic frame is an isometric map from the hyperbolic space. -/
theorem form_hyperbolicFrameMap [RingHomInvPair σ σ] [Fintype ι] (hxy : H.IsHyperbolicFrame x y)
    (u v : (ι → K) × (ι → K)) :
    H.form (hyperbolicFrameMap K x y u) (hyperbolicFrameMap K x y v) =
      (SignedHermitianSpace.hyperbolic K σ ε ι).form u v := by
  rw [hyperbolicFrameMap_apply, hyperbolicFrameMap_apply]
  simp only [map_add, map_sum, map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hxy.form_left, hxy.form_right, hxy.form_left_right,
    hxy.form_right_left, mul_zero, zero_add, add_zero, mul_ite,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, RingHom.id_apply, hyperbolic_form_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ ↦ by rw [Units.smul_def, zsmul_eq_mul]; ring

/-- The map `H^ι → V` of a hyperbolic frame is injective. -/
theorem injective_hyperbolicFrameMap [RingHomInvPair σ σ] [Fintype ι]
    (hxy : H.IsHyperbolicFrame x y) : Function.Injective (hyperbolicFrameMap K x y) :=
  injective_of_form_apply_eq (K := K) (H₁ := SignedHermitianSpace.hyperbolic K σ ε ι) (H₂ := H)
    hxy.form_hyperbolicFrameMap

/-- The first family of a hyperbolic frame is linearly independent. -/
theorem linearIndependent_left [RingHomInvPair σ σ] [Finite ι] (hxy : H.IsHyperbolicFrame x y) :
    LinearIndependent K x := by
  cases nonempty_fintype ι
  refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
  have := hxy.injective_hyperbolicFrameMap (a₁ := (c, 0)) (a₂ := 0) (by
    simpa [hyperbolicFrameMap_apply] using hc)
  exact congrFun (congrArg Prod.fst this)

end IsHyperbolicFrame

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* K} {ε : ℤˣ}
  {H : SignedHermitianSpace K V σ ε}

/-- Over a field, a vector is isotropic exactly when it is nonzero with `h x x = 0`. -/
theorem isIsotropic_iff {x : V} : H.IsIsotropic x ↔ H.form x x = 0 ∧ x ≠ 0 :=
  and_congr_right fun _ ↦ ⟨fun h hx ↦ one_ne_zero (h 1 (by simp [hx])),
    fun hx _ hc ↦ (smul_eq_zero.1 hc).resolve_right hx⟩

variable [RingHomInvPair σ σ]

/-- The triangular correction making a dual frame isotropic: for a matrix `G` with
`σ (G j i) = ε • G i j`, some `μ` has `G i j + ε • μ i j + σ (μ j i) = 0` for all `i`, `j`. -/
private theorem exists_add_smul_add_eq_zero (hσ : ∃ z, σ z ≠ z) {ι : Type*} [LinearOrder ι]
    {G : ι → ι → K} (hG : ∀ i j, σ (G j i) = ε • G i j) :
    ∃ μ : ι → ι → K, ∀ i j, G i j + ε • μ i j + σ (μ j i) = 0 := by
  have hσσ (a : K) : σ (σ a) = a := RingHomInvPair.comp_apply_eq₂
  -- On the diagonal, `-G i i = s + ε σ s`; take `μ i i = σ s`.
  choose s hs using fun i ↦ exists_units_add_smul_eq hσ (c := -G i i) (by
    rw [map_neg, hG i i, smul_neg])
  refine ⟨fun i j ↦ if i < j then -(ε • G i j) else if i = j then σ (s i) else 0, fun i j ↦ ?_⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij, hij.not_gt, hij.ne', smul_smul]
  · simp only [lt_irrefl, ↓reduceIte, hσσ]
    rw [add_assoc, add_comm (ε • σ _), hs i, add_neg_cancel]
  · simp [hij, hij.not_gt, hij.ne', hG, smul_smul]

/-- **Hyperbolic frames from isotropic frames.** Over a field whose involution is not the
identity, a finite linearly independent family `x` spanning a totally isotropic subspace is the
first half of a hyperbolic frame. The space need not be finite-dimensional. -/
theorem exists_isHyperbolicFrame (hσ : ∃ z, σ z ≠ z) {ι : Type*} [Finite ι] [DecidableEq ι]
    {x : ι → V} (hx : LinearIndependent K x) (hxx : ∀ i j, H.form (x i) (x j) = 0) :
    ∃ y, H.IsHyperbolicFrame x y := by
  cases nonempty_fintype ι
  have hε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  -- Dual vectors `e j` with `h (x i) (e j) = δᵢⱼ`.
  choose u hu using H.exists_form_apply_eq_ite hx
  set e : ι → V := fun j ↦ ((ε : ℤ) : K) • u j
  have hxe (i j : ι) : H.form (x i) (e j) = if i = j then 1 else 0 := by
    simp only [e, map_smul, smul_eq_mul, H.form_swap (u j), hu, Units.smul_def, zsmul_eq_mul]
    split_ifs <;> simp [*]
  have hex (i j : ι) : H.form (e i) (x j) = if i = j then ((ε : ℤ) : K) else 0 := by
    rw [H.form_swap, hxe, Units.smul_def, zsmul_eq_mul]
    split_ifs <;> simp_all [eq_comm]
  -- Correct `e j` by `∑ μ i j • x i`.
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → ι → K, ∀ i j, H.form (e i) (e j) + ε • μ i j + σ (μ j i) = 0 := by
    let _ : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
    exact exists_add_smul_add_eq_zero hσ fun i j ↦ by
      rw [H.form_swap (e i), map_zsmul_unit, RingHomInvPair.comp_apply_eq₂]
  set y : ι → V := fun j ↦ e j + ∑ i, μ i j • x i
  have hxy (i j : ι) : H.form (x i) (y j) = if i = j then 1 else 0 := by
    simp [y, map_sum, hxx, hxe]
  refine ⟨y, ⟨hxx, fun i j ↦ ?_, hxy⟩⟩
  have hey : H.form (e i) (y j) = H.form (e i) (e j) + ε • μ i j := by
    change H.form (e i) (e j + ∑ k, μ k j • x k) = _
    simp [map_sum, hex, Units.smul_def, zsmul_eq_mul, mul_comm]
  have hyy : H.form (y i) (y j) = H.form (e i) (y j) + σ (μ j i) := by
    change H.form (e i + ∑ k, μ k i • x k) (y j) = _
    simp [map_sum, hxy]
  rw [hyy, hey]
  exact hμ i j

/-- **Every isotropic vector lies in a hyperbolic plane.** Over a field whose involution is not
the identity, for every nonzero `x` with `h x x = 0` there is `y` with `h y y = 0` and
`h x y = 1`. -/
theorem exists_form_eq_zero_form_eq_one (hσ : ∃ z, σ z ≠ z) {x : V} (hx : H.IsIsotropic x) :
    ∃ y, H.form y y = 0 ∧ H.form x y = 1 := by
  obtain ⟨y, hy⟩ := exists_isHyperbolicFrame (ι := Fin 1) (H := H) hσ (x := fun _ ↦ x)
    (linearIndependent_unique_iff.2 (isIsotropic_iff.1 hx).2) fun _ _ ↦ hx.1
  exact ⟨y 0, hy.form_right 0 0, by simpa using hy.form_left_right 0 0⟩

namespace IsHyperbolicFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {x y : ι → V}

/-- The span of a hyperbolic frame is a nondegenerate subspace. -/
theorem separatingLeft_domRestrict_range (hxy : H.IsHyperbolicFrame x y) :
    (H.form.domRestrict₁₂ (LinearMap.range (hyperbolicFrameMap K x y))
      (LinearMap.range (hyperbolicFrameMap K x y))).SeparatingLeft := by
  rintro ⟨_, u, rfl⟩ hu
  have : u = 0 := (SignedHermitianSpace.hyperbolic K σ ε ι).separatingLeft u fun v ↦ by
    have := hu ⟨_, v, rfl⟩
    rwa [LinearMap.domRestrict₁₂_apply, hxy.form_hyperbolicFrameMap] at this
  simp [this]

/-- **Splitting off a hyperbolic frame.** If `x`, `y` is a hyperbolic frame of `(V, h)` and `P`
its span, then `V ≅ H^ι ⊥ Pᗮ`. -/
theorem equivalent_hyperbolic_prod (hxy : H.IsHyperbolicFrame x y) :
    Equivalent H ((SignedHermitianSpace.hyperbolic K σ ε ι).prod
      (H.restrict ((LinearMap.range (hyperbolicFrameMap K x y)).orthogonalBilin H.form)
        (H.separatingLeft_domRestrict_orthogonalBilin hxy.separatingLeft_domRestrict_range))) := by
  refine (H.equivalent_restrict_prod_orthogonalBilin hxy.separatingLeft_domRestrict_range).trans
    (Equivalent.prod (Equivalent.symm (IsometryEquiv.equivalent ?_)) (Equivalent.refl _))
  exact { LinearEquiv.ofInjective _ hxy.injective_hyperbolicFrameMap with
    map_app' := fun u v ↦ by simp [← hxy.form_hyperbolicFrameMap] }

end IsHyperbolicFrame

end Field

end SignedHermitianSpace

end TauCeti
