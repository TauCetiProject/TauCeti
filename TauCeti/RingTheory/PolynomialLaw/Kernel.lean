/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The kernel of a polynomial law

For an `R`-polynomial law `f : M →ₚₗ[R] N`, the kernel `Ker(f) ⊆ M` is the set of `x ∈ M` such
that `f_S(b ⊗ x + m) = f_S(m)` for every commutative `R`-algebra `S`, every `b ∈ S` and every
`m ∈ S ⊗[R] M`. It is an `R`-submodule of `M`, and `f` is *faithful* if `Ker(f) = 0`.

The kernel is the largest submodule through which `f` factors: for a submodule `K` of `M`, the
law `f` is `g ∘ π` for a polynomial law `g : M ⧸ K →ₚₗ[R] N`, where `π` is the law of the
quotient map, exactly when `K ≤ Ker(f)`. The law induced on `M ⧸ Ker(f)` is faithful.

The algebras `S` range over the universe of `R`, as in the components `PolynomialLaw.toFun'`,
which determine the law; `PolynomialLaw.toFun_add_tmul_of_mem_ker` gives the defining property
for algebras in any universe.

## Main declarations

* `PolynomialLaw.ker f`: the kernel of `f`, an `R`-submodule of `M`.
* `PolynomialLaw.IsFaithful f`: `f` has kernel `0`.
* `PolynomialLaw.ker_zero`, `LinearMap.ker_toPolynomialLaw`, `PolynomialLaw.isFaithful_id`: the
  zero law has kernel `M`, the kernel of the law of a linear map is its kernel, and the identity
  law is faithful.
* `PolynomialLaw.liftQ f K hK`: the law on `M ⧸ K` induced by `f` when `K ≤ Ker(f)`, with
  `PolynomialLaw.liftQ_comp_mkQ`.
* `PolynomialLaw.exists_eq_comp_mkQ_iff_le_ker`: `f` factors through `M ⧸ K` iff `K ≤ Ker(f)`.
* `PolynomialLaw.ker_liftQ`: the kernel of `f.liftQ K hK` is the image of `Ker(f)` in `M ⧸ K`.
* `PolynomialLaw.isFaithful_liftQ_ker`: the law induced on `M ⧸ Ker(f)` is faithful.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*](https://arxiv.org/abs/0809.0415), §1.17 and
  Lemma 1.18, p. 16
-/

public section

noncomputable section

universe u

open TensorProduct LinearMap

namespace PolynomialLaw

section CommSemiring

variable {R : Type u} [CommSemiring R] {M N P : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]

/-- The **kernel** of a polynomial law `f : M →ₚₗ[R] N`: the `x ∈ M` with
`f_S(b ⊗ x + m) = f_S(m)` for every commutative `R`-algebra `S`, `b ∈ S` and `m ∈ S ⊗[R] M`. -/
def ker (f : M →ₚₗ[R] N) : Submodule R M where
  carrier := {x | ∀ (S : Type u) [CommSemiring S] [Algebra R S] (b : S) (m : S ⊗[R] M),
    f.toFun' S (b ⊗ₜ x + m) = f.toFun' S m}
  add_mem' {x y} hx hy S _ _ b m := by
    rw [Set.mem_ofPred_eq] at hx hy
    rw [tmul_add, add_assoc, hx, hy]
  zero_mem' S _ _ b m := by
    rw [tmul_zero, zero_add]
  smul_mem' r x hx S _ _ b m := by
    rw [Set.mem_ofPred_eq] at hx
    rw [← smul_tmul, hx]

theorem mem_ker {f : M →ₚₗ[R] N} {x : M} :
    x ∈ f.ker ↔ ∀ (S : Type u) [CommSemiring S] [Algebra R S] (b : S) (m : S ⊗[R] M),
      f.toFun' S (b ⊗ₜ x + m) = f.toFun' S m :=
  Iff.rfl

/-- A polynomial law is **faithful** if its kernel is `0`. -/
def IsFaithful (f : M →ₚₗ[R] N) : Prop :=
  f.ker = ⊥

theorem isFaithful_iff (f : M →ₚₗ[R] N) : f.IsFaithful ↔ f.ker = ⊥ :=
  Iff.rfl

/-- The zero law has kernel everything. -/
@[simp]
theorem ker_zero : (0 : M →ₚₗ[R] N).ker = ⊤ :=
  eq_top_iff.mpr fun _ _ S _ _ _ _ ↦ by simp

/-- The kernel of `f` lies in the kernel of every composite `g ∘ f`. -/
theorem ker_le_ker_comp (g : N →ₚₗ[R] P) (f : M →ₚₗ[R] N) : f.ker ≤ (g.comp f).ker :=
  fun _ hx S _ _ b m ↦ by
    rw [comp_toFun', Function.comp_apply, Function.comp_apply, hx]

/-- Adding an element of the image of `S ⊗ K` does not change `f_S` when `K ≤ Ker(f)`. -/
theorem toFun'_add_lTensor_subtype {f : M →ₚₗ[R] N} {K : Submodule R M} (hK : K ≤ f.ker)
    (S : Type u) [CommSemiring S] [Algebra R S] (m : S ⊗[R] M) (t : S ⊗[R] K) :
    f.toFun' S (m + K.subtype.lTensor S t) = f.toFun' S m := by
  induction t generalizing m with
  | tmul b k => rw [lTensor_tmul, Submodule.subtype_apply, add_comm, hK k.property S b m]
  | add t₁ t₂ h₁ h₂ => rw [map_add, ← add_assoc, h₂, h₁]

/-- The defining property of `x ∈ Ker(f)` for algebras `S` in any universe:
`f_S(b ⊗ x + m) = f_S(m)` for every `b ∈ S` and `m ∈ S ⊗ M`. -/
theorem toFun_add_tmul_of_mem_ker {f : M →ₚₗ[R] N} {x : M} (hx : x ∈ f.ker) (S : Type*)
    [CommSemiring S] [Algebra R S] (b : S) (m : S ⊗[R] M) :
    f.toFun S (b ⊗ₜ x + m) = f.toFun S m := by
  obtain ⟨n, ψ, p, q, rfl, rfl⟩ := exists_lift' m b
  rw [← AlgHom.toLinearMap_apply, ← rTensor_tmul, ← map_add, ← isCompat_apply,
    ← toFun'_eq_toFun, hx, toFun'_eq_toFun, isCompat_apply]

end CommSemiring

end PolynomialLaw

namespace LinearMap

variable {R : Type u} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- The kernel of the polynomial law of a linear map `u` is the kernel of `u`. -/
@[simp]
theorem ker_toPolynomialLaw (u : M →ₗ[R] N) : u.toPolynomialLaw.ker = LinearMap.ker u := by
  ext x
  refine ⟨fun hx ↦ ?_, fun hx S _ _ b m ↦ ?_⟩
  · have h := hx R 1 0
    rw [add_zero, toPolynomialLaw_toFun', baseChange_tmul, map_zero] at h
    rw [LinearMap.mem_ker]
    simpa using congr(TensorProduct.lid R N $h)
  · rw [toPolynomialLaw_toFun', map_add, baseChange_tmul, LinearMap.mem_ker.mp hx, tmul_zero,
      zero_add]

end LinearMap

namespace PolynomialLaw

section CommSemiring

variable {R : Type u} [CommSemiring R] {M : Type*} [AddCommMonoid M] [Module R M]

/-- The identity law has kernel `0`. -/
@[simp]
theorem ker_id : (PolynomialLaw.id : M →ₚₗ[R] M).ker = ⊥ := by
  rw [← LinearMap.toPolynomialLaw_id, LinearMap.ker_toPolynomialLaw, LinearMap.ker_id]

/-- The identity law is faithful. -/
theorem isFaithful_id : (PolynomialLaw.id : M →ₚₗ[R] M).IsFaithful :=
  ker_id

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommMonoid N] [Module R N] {f : M →ₚₗ[R] N} {K : Submodule R M}

/-- When `K ≤ Ker(f)`, `f_S` is constant on the fibres of `S ⊗ M → S ⊗ (M ⧸ K)`. -/
theorem toFun'_eq_of_lTensor_mkQ_eq (hK : K ≤ f.ker) (S : Type u) [CommSemiring S]
    [Algebra R S] {m m' : S ⊗[R] M} (h : K.mkQ.lTensor S m = K.mkQ.lTensor S m') :
    f.toFun' S m = f.toFun' S m' := by
  -- `lTensor_exact` and the subtraction `m - m'` need `S` to be an additive group; over the
  -- ring `R` it is one, with negation `(-1) • ·`, extending the given `AddCommMonoid`.
  let _ : AddCommGroup S := Module.addCommMonoidToAddCommGroup R
  have hex : Function.Exact (K.subtype.lTensor S) (K.mkQ.lTensor S) :=
    lTensor_exact S (LinearMap.exact_subtype_mkQ K) K.mkQ_surjective
  obtain ⟨t, ht⟩ := (hex (m - m')).mp (by rw [map_sub, h, sub_self])
  rw [← toFun'_add_lTensor_subtype hK S m' t, ht, add_sub_cancel]

/-- The polynomial law on `M ⧸ K` induced by `f` when `K ≤ Ker(f)`: its component at `S` sends
`y ∈ S ⊗ (M ⧸ K)` to `f_S(m)` for any preimage `m ∈ S ⊗ M` of `y`. -/
def liftQ (f : M →ₚₗ[R] N) (K : Submodule R M) (hK : K ≤ f.ker) : (M ⧸ K) →ₚₗ[R] N where
  toFun' S _ _ y := f.toFun' S (Function.surjInv (K.mkQ.lTensor_surjective S K.mkQ_surjective) y)
  isCompat' {S _ _ S' _ _} φ := funext fun y ↦ by
    simp only [Function.comp_apply, isCompat_apply']
    refine toFun'_eq_of_lTensor_mkQ_eq hK S' ?_
    rw [Function.surjInv_eq (K.mkQ.lTensor_surjective S' K.mkQ_surjective)]
    conv_rhs => rw [← Function.surjInv_eq (K.mkQ.lTensor_surjective S K.mkQ_surjective) y]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, lTensor_comp_rTensor,
      rTensor_comp_lTensor]

/-- The component of `f.liftQ K hK` at `S` evaluated at the image of `m ∈ S ⊗ M` is `f_S(m)`. -/
@[simp]
theorem liftQ_toFun'_lTensor_mkQ (hK : K ≤ f.ker) (S : Type u) [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] M) : (f.liftQ K hK).toFun' S (K.mkQ.lTensor S m) = f.toFun' S m :=
  toFun'_eq_of_lTensor_mkQ_eq hK S
    (Function.surjInv_eq (K.mkQ.lTensor_surjective S K.mkQ_surjective) _)

/-- `f` is the composite of `f.liftQ K hK` with the law of the quotient map `M → M ⧸ K`. -/
@[simp]
theorem liftQ_comp_mkQ (hK : K ≤ f.ker) : (f.liftQ K hK).comp K.mkQ.toPolynomialLaw = f := by
  ext S _ _ m
  rw [comp_toFun', Function.comp_apply, LinearMap.toPolynomialLaw_toFun', baseChange_eq_lTensor,
    liftQ_toFun'_lTensor_mkQ]

/-- The `toFun` form of `liftQ_toFun'_lTensor_mkQ`, for algebras `S` in any universe: the
component of `f.liftQ K hK` at `S` evaluated at the image of `m ∈ S ⊗ M` is `f_S(m)`. -/
@[simp]
theorem liftQ_toFun_lTensor_mkQ (hK : K ≤ f.ker) (S : Type*) [CommSemiring S] [Algebra R S]
    (m : S ⊗[R] M) : (f.liftQ K hK).toFun S (K.mkQ.lTensor S m) = f.toFun S m := by
  rw [← baseChange_eq_lTensor, ← LinearMap.toPolynomialLaw_toFun, ← toFun_comp_apply,
    liftQ_comp_mkQ]

/-- On `M`, the law `f.liftQ K hK` sends the class of `x` to `f(x)`. -/
@[simp]
theorem ground_liftQ_mk (hK : K ≤ f.ker) (x : M) :
    (f.liftQ K hK).ground (Submodule.Quotient.mk x) = f.ground x := by
  rw [ground_apply, ground_apply, ← Submodule.mkQ_apply, ← lTensor_tmul,
    liftQ_toFun'_lTensor_mkQ]

/-- A law on `M ⧸ K` is determined by its composite with the law of the quotient map. -/
@[ext high]
theorem ext_mkQ ⦃g g' : (M ⧸ K) →ₚₗ[R] N⦄
    (h : g.comp K.mkQ.toPolynomialLaw = g'.comp K.mkQ.toPolynomialLaw) : g = g' := by
  ext S _ _ y
  obtain ⟨m, rfl⟩ := K.mkQ.lTensor_surjective S K.mkQ_surjective y
  simpa [comp_toFun', LinearMap.toPolynomialLaw_toFun', baseChange_eq_lTensor] using
    congrArg (fun F : M →ₚₗ[R] N ↦ F.toFun' S m) h

/-- Composing with the law of the quotient map `M → M ⧸ K` is injective. -/
theorem comp_mkQ_injective :
    Function.Injective fun g : (M ⧸ K) →ₚₗ[R] N ↦ g.comp K.mkQ.toPolynomialLaw :=
  ext_mkQ

/-- **The kernel is the largest submodule through which a law factors**: `f` factors through the
quotient map `M → M ⧸ K` exactly when `K ≤ Ker(f)`. -/
theorem exists_eq_comp_mkQ_iff_le_ker :
    (∃ g : (M ⧸ K) →ₚₗ[R] N, f = g.comp K.mkQ.toPolynomialLaw) ↔ K ≤ f.ker := by
  refine ⟨?_, fun hK ↦ ⟨f.liftQ K hK, (liftQ_comp_mkQ hK).symm⟩⟩
  rintro ⟨g, rfl⟩
  exact (LinearMap.ker_toPolynomialLaw K.mkQ ▸ (Submodule.ker_mkQ K).ge).trans
    (ker_le_ker_comp g _)

/-- The kernel of the law induced on `M ⧸ K` is the image of `Ker(f)` in `M ⧸ K`. -/
@[simp]
theorem ker_liftQ (hK : K ≤ f.ker) : (f.liftQ K hK).ker = f.ker.map K.mkQ := by
  have h : (f.liftQ K hK).ker.comap K.mkQ = f.ker := by
    ext x
    refine ⟨fun hx S _ _ b m ↦ ?_, fun hx S _ _ b y ↦ ?_⟩
    · rw [← liftQ_toFun'_lTensor_mkQ hK S (b ⊗ₜ x + m), ← liftQ_toFun'_lTensor_mkQ hK S m,
        map_add, lTensor_tmul]
      exact hx S b _
    · obtain ⟨m, rfl⟩ := K.mkQ.lTensor_surjective S K.mkQ_surjective y
      have := hx S b m
      rwa [← liftQ_toFun'_lTensor_mkQ hK, ← liftQ_toFun'_lTensor_mkQ hK S m, map_add,
        lTensor_tmul] at this
  rw [← h, Submodule.map_comap_eq_of_surjective K.mkQ_surjective]

/-- **The law induced on `M ⧸ Ker(f)` is faithful.** -/
theorem isFaithful_liftQ_ker : (f.liftQ f.ker le_rfl).IsFaithful := by
  rw [isFaithful_iff, ker_liftQ, Submodule.mkQ_map_self]

end CommRing

end PolynomialLaw
