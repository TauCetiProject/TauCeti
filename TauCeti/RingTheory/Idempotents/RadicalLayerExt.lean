/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Projective.RadicalExt
public import TauCeti.RingTheory.Idempotents.Module
public import TauCeti.RingTheory.Idempotents.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
import TauCeti.RingTheory.Idempotents.Jacobson
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Extensions between simple tops and corners of the first radical layer

Let `A` be an algebra over a field `k`, with Jacobson radical `J`, and let `e : ι → A` be a
complete family of orthogonal idempotents whose classes span `A ⧸ J` over `k`. This is the
situation of a basic algebra over an algebraically closed field
(`TauCeti.IsBasic.exists_completeOrthogonalIdempotents`), and of a bound quiver algebra with its
vertex idempotents: `A ⧸ J` is then one copy of `k` for each index. Write
`Sᵢ = Aeᵢ / J(Aeᵢ)` for the top of the projective left ideal `Aeᵢ`. This file proves

`Ext¹_A(Sᵢ, Sⱼ) ≃ Homₖ(eⱼ (J / J²) eᵢ, k)`,

so that `dimₖ Ext¹_A(Sᵢ, Sⱼ)` is the dimension of the `(j, i)`-corner of the first radical
layer `J / J²`. A basis of that corner is the set of arrows `i → j` of the quiver of a basic
algebra, as in its bound-quiver presentation
(`TauCeti.IsBasic.exists_surjective_pathAlgebra_isAdmissibleIdeal_ker`), so the arrow counts of
that quiver are those of the Ext-quiver.

The proof has three steps.

* A module `M` killed by `J` is a module over `A ⧸ J`, a product of copies of `k`, so an
  `A`-linear map from `M` to a module on which `eⱼ` acts as the identity is the same as a
  `k`-linear map out of the piece `eⱼ M`
  (`CompleteOrthogonalIdempotents.linearMapEquivSMulTopLinearMap`). The top `Sⱼ` is such a
  module, and it is the line spanned by the class of `eⱼ`
  (`CompleteOrthogonalIdempotents.equivQuotientSMulTop`).
* For idempotents `f` and `g` and any two-sided ideal `J`, the piece `f M` of the first radical
  layer `M = J(Ag) / J²(Ag)` of `Ag` is the corner `f (J / J²) g`
  (`IsIdempotentElem.smulTopRadicalLayerEquiv`).
* The extensions of `Sᵢ` are computed from the first radical layer of `Aeᵢ` by
  `Submodule.radicalLayerHomEquivExt`.

## Main definitions

* `TauCeti.radicalLayerCorner k J f g`: the corner `f (J / J²) g` as a `k`-subspace of
  `A ⧸ J ^ 2`.
* `IsIdempotentElem.smulTopRadicalLayerEquiv`: for idempotents `f` and `g`, the piece `f M` of
  the first radical layer `M` of `Ag` is the corner `f (J / J²) g`.
* `CompleteOrthogonalIdempotents.linearMapEquivSMulTopLinearMap`: maps from a module killed by
  `J` into one on which `eⱼ` is the identity are `k`-linear maps out of the piece `eⱼ M`.
* `CompleteOrthogonalIdempotents.equivQuotientSMulTop`: the top `Sⱼ` is the line `k [eⱼ]`.
* `CompleteOrthogonalIdempotents.extQuotientSMulTopEquivDual`: the linear equivalence
  `Ext¹_A(Sᵢ, Sⱼ) ≃ₗ[k] Dual k (eⱼ (J / J²) eᵢ)`.

## Main results

* `CompleteOrthogonalIdempotents.finrank_ext_quotient_smul_top`: `dimₖ Ext¹_A(Sᵢ, Sⱼ)` is the
  dimension of the corner `eⱼ (J / J²) eᵢ`.
* `CompleteOrthogonalIdempotents.isSimpleModule_quotient_smul_top` and
  `CompleteOrthogonalIdempotents.finrank_quotient_smul_top`: each top `Sⱼ` with `eⱼ ∉ J` is a
  simple module of dimension one.

## Implementation notes

The Ext comparison takes `k` and `A` in one universe: `Ext` is computed in `ModuleCat A` by
`Submodule.radicalLayerHomEquivExt`, whose module universe must contain both the base field and
the left ideals `Aeᵢ`. The `k`-module structure on `Ext` is the one `ModuleCat` puts on its
objects (`ModuleCat.Algebra`), which is not definitionally the quotient-module structure on
`Sⱼ`; the general statements are therefore stated for arbitrary compatible `k`-module
structures.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Lemma III.2.12, and Section II.3 for the quiver of a basic algebra.
-/

public section

open CategoryTheory CategoryTheory.Abelian
open scoped Pointwise

namespace TauCeti

section Corner

variable (k : Type*) {A : Type*} [CommSemiring k] [Ring A] [Algebra k A]

/-- The corner `f (J / J²) g` of the first radical layer `J / J²`, as a `k`-subspace of
`A ⧸ J ^ 2`: the classes of the elements `f x g` with `x ∈ J`. For idempotents `eⱼ` and `eᵢ`
this is the `(j, i)`-corner whose basis gives the arrows `i → j` of the quiver of `A`. -/
def radicalLayerCorner (J : Ideal A) [J.IsTwoSided] (f g : A) : Submodule k (A ⧸ J ^ 2) :=
  (J.restrictScalars k).map
    ((Ideal.Quotient.mkₐ k (J ^ 2)).toLinearMap ∘ₗ LinearMap.mulLeftRight k (f, g))

variable {k}

@[simp]
theorem mem_radicalLayerCorner {J : Ideal A} [J.IsTwoSided] {f g : A} {z : A ⧸ J ^ 2} :
    z ∈ radicalLayerCorner k J f g ↔ ∃ x ∈ J, Ideal.Quotient.mk (J ^ 2) (f * x * g) = z := by
  simp [radicalLayerCorner, Ideal.Quotient.mkₐ_eq_mk]

end Corner

/-- Ideal squares over a noncommutative ring are products. -/
private theorem sq_eq_mul {A : Type*} [Ring A] (J : Ideal A) [J.IsTwoSided] : J ^ 2 = J * J := by
  rw [show (2 : ℕ) = 1 + 1 by omega, Ideal.IsTwoSided.pow_succ, Submodule.pow_one]

/-- The elements of `J • N` lie in `J`. -/
private theorem coe_mem_of_mem_smul {A : Type*} [Ring A] {J : Ideal A} [J.IsTwoSided]
    {P : Submodule A A} {N : Submodule A P} {y : P}
    (hy : y ∈ J • N) : (y : A) ∈ J :=
  Submodule.smul_induction_on hy (fun r hr n _ ↦ J.mul_mem_right _ hr)
    fun _ _ h₁ h₂ ↦ by simpa using J.add_mem h₁ h₂

/-- The elements of `J • (J • N)` lie in `J ^ 2`. -/
private theorem coe_mem_sq_of_mem_smul {A : Type*} [Ring A] {J : Ideal A} [J.IsTwoSided]
    {P : Submodule A A} {K : Submodule A P}
    {N : Submodule A P} (hK : K ≤ J • N) {y : K} (hy : y ∈ J • (⊤ : Submodule A K)) :
    ((y : P) : A) ∈ J ^ 2 :=
  Submodule.smul_induction_on hy
    (fun r hr n _ ↦ by
      rw [sq_eq_mul J]
      exact Ideal.mul_mem_mul hr (coe_mem_of_mem_smul (hK n.property)))
    fun _ _ h₁ h₂ ↦ by simpa using (J ^ 2).add_mem h₁ h₂

end TauCeti

namespace IsIdempotentElem

open TauCeti

variable {k : Type*} {A : Type*} [CommRing k] [Ring A] [Algebra k A]
  {J : Ideal A} [J.IsTwoSided] {f g : A}

variable (k J) in
/-- The `k`-linear map from the first radical layer `J(Ag) / J²(Ag)` of the left ideal `Ag` to
`A ⧸ J ^ 2`, sending a class to the class of the underlying element of `A`. -/
private noncomputable def radicalLayerToQuotient (g : A) :
    (↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))) ⧸
        J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))) →ₗ[k]
      A ⧸ J ^ 2 :=
  (Submodule.liftQ _ ((J ^ 2).mkQ ∘ₗ (Ideal.span {g} : Ideal A).subtype ∘ₗ
    (J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))).subtype) fun y hy ↦ by
      simpa [Submodule.Quotient.mk_eq_zero, Ideal.Quotient.eq_zero_iff_mem] using
        coe_mem_sq_of_mem_smul le_rfl hy)
    |>.restrictScalars k

private theorem radicalLayerToQuotient_mk
    (y : ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A)))) :
    radicalLayerToQuotient k J g (Submodule.Quotient.mk y) =
      Ideal.Quotient.mk (J ^ 2) ((y : (Ideal.span {g} : Ideal A)) : A) :=
  (rfl)

omit [Algebra k A] in
/-- Every element of `J ^ 2 g` is the underlying element of some element of `J • (J • Ag)`. -/
private theorem exists_mem_smul_coe_eq_mul {z : A} (hz : z ∈ J ^ 2) :
    ∃ t ∈ J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A)))),
      ((t : (Ideal.span {g} : Ideal A)) : A) = z * g := by
  rw [sq_eq_mul J] at hz
  refine Submodule.mul_induction_on hz (fun r hr s hs ↦ ?_) fun z₁ z₂ ⟨t₁, ht₁, h₁⟩
    ⟨t₂, ht₂, h₂⟩ ↦ ⟨t₁ + t₂, add_mem ht₁ ht₂, by simp [h₁, h₂, add_mul]⟩
  have hsg : s • spanSingletonGenerator g ∈ J • (⊤ : Submodule A (Ideal.span {g} : Ideal A)) :=
    Submodule.smul_mem_smul hs Submodule.mem_top
  exact ⟨r • ⟨_, hsg⟩, Submodule.smul_mem_smul hr Submodule.mem_top, by simp [mul_assoc]⟩

/-- **The corners of the first radical layer.** For idempotents `f` and `g` and a two-sided ideal
`J`, the piece `f M` of the first radical layer `M = J(Ag) / J²(Ag)` of the left ideal `Ag` is
the corner `f (J / J²) g`, by sending a class to the class of the underlying element of `A`. -/
noncomputable def smulTopRadicalLayerEquiv (hf : IsIdempotentElem f) (hg : IsIdempotentElem g) :
    ↥(f • (⊤ : Submodule k (↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))) ⧸
        J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))))) ≃ₗ[k]
      radicalLayerCorner k J f g := by
  set P := (Ideal.span {g} : Ideal A)
  set K := J • (⊤ : Submodule A P)
  set φ := radicalLayerToQuotient k J g ∘ₗ
    (f • (⊤ : Submodule k (K ⧸ J • (⊤ : Submodule A K)))).subtype
  -- `φ` is injective because every element of `J ^ 2 g` comes from `J • K`, and its range is
  -- the corner because every element of `K` lies in `J` and is fixed by right multiplication
  -- by `g`.
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).mpr ?_
    rintro ⟨m, hm⟩ hφ
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have hfm := (hf.mem_smul_top_iff_smul_eq_self (S := k)).mp hm
    rw [← Submodule.Quotient.mk_smul] at hfm
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply] at hφ
    rw [← hfm, radicalLayerToQuotient_mk, Ideal.Quotient.eq_zero_iff_mem] at hφ
    obtain ⟨t, ht, hte⟩ := exists_mem_smul_coe_eq_mul hφ
    have hfy : f • y = t := by
      refine Subtype.ext (Subtype.ext ?_)
      rw [hte]
      simp [mul_assoc, (mem_span_singleton_iff_mul_eq_self hg).mp (y : P).property]
    refine Subtype.ext ?_
    simpa [← hfm, hfy, Submodule.Quotient.mk_eq_zero] using ht
  have hrange : LinearMap.range φ = radicalLayerCorner k J f g := by
    apply le_antisymm
    · rintro _ ⟨⟨m, hm⟩, rfl⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have hfm := (hf.mem_smul_top_iff_smul_eq_self (S := k)).mp hm
      rw [← Submodule.Quotient.mk_smul] at hfm
      refine mem_radicalLayerCorner.mpr ⟨(y : P), coe_mem_of_mem_smul y.property, ?_⟩
      simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [← hfm, radicalLayerToQuotient_mk]
      congr 1
      simp [mul_assoc, (mem_span_singleton_iff_mul_eq_self hg).mp (y : P).property]
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := mem_radicalLayerCorner.mp hz
      have hxg : x • spanSingletonGenerator g ∈ K := Submodule.smul_mem_smul hx Submodule.mem_top
      let m : K ⧸ J • (⊤ : Submodule A K) := f • Submodule.Quotient.mk ⟨_, hxg⟩
      have hm : m ∈ f • (⊤ : Submodule k (K ⧸ J • (⊤ : Submodule A K))) :=
        Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
      refine ⟨⟨m, hm⟩, ?_⟩
      simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, m]
      rw [← Submodule.Quotient.mk_smul, radicalLayerToQuotient_mk]
      congr 1
      simp [mul_assoc, coe_spanSingletonGenerator]
  exact (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hrange)

@[simp]
theorem coe_smulTopRadicalLayerEquiv_mk (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (y : ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))
    (hy : Submodule.Quotient.mk y ∈ f • (⊤ : Submodule k
      (↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))) ⧸
        J • (⊤ : Submodule A ↥(J • (⊤ : Submodule A (Ideal.span {g} : Ideal A))))))) :
    (smulTopRadicalLayerEquiv hf hg ⟨_, hy⟩ : A ⧸ J ^ 2) =
      Ideal.Quotient.mk (J ^ 2) ((y : (Ideal.span {g} : Ideal A)) : A) :=
  radicalLayerToQuotient_mk (k := k) y

end IsIdempotentElem

namespace CompleteOrthogonalIdempotents

open TauCeti

section Hom

variable {k : Type*} {A : Type*} [CommRing k] [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] {e : ι → A} {J : Ideal A} [J.IsTwoSided]
  {M N : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- If the classes of the `e i` span `A ⧸ J` over `k`, then for every `a` and `j` there is a
scalar `c` with `e j * a ≡ c • e j ≡ a * e j` modulo `J`. -/
private theorem exists_mul_sub_smul_mem (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤) (a : A)
    (j : ι) : ∃ c : k, e j * a - c • e j ∈ J ∧ a * e j - c • e j ∈ J := by
  classical
  have ha : Ideal.Quotient.mk J a ∈
      Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) :=
    hquot ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp ha
  have hmem : a - ∑ i, c i • e i ∈ J := by
    refine Ideal.Quotient.eq.mp ?_
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk k, map_smul]
  have hl : e j * ∑ i, c i • e i = c j • e j := by
    simp [Finset.mul_sum, he.mul_eq]
  have hr : (∑ i, c i • e i) * e j = c j • e j := by
    simp [Finset.sum_mul, he.mul_eq]
  refine ⟨c j, ?_, ?_⟩
  · rw [← hl, ← mul_sub]
    exact J.mul_mem_left _ hmem
  · rw [← hr, ← sub_mul]
    exact J.mul_mem_right _ hmem

omit [Fintype ι] [J.IsTwoSided] in
/-- On a vector fixed by `e j` in a module killed by `J`, an element `a` acts as the scalar `c`
with `a * e j ≡ c • e j` modulo `J`. -/
private theorem smul_eq_smul_of_smul_eq_self (hN : Module.IsTorsionBySet A N J) {a : A} {c : k}
    {j : ι} (hr : a * e j - c • e j ∈ J) {n : N} (hn : e j • n = n) : a • n = c • n :=
  calc a • n = a • e j • n := by rw [hn]
    _ = (a * e j - c • e j) • n + (c • e j) • n := by rw [← add_smul, sub_add_cancel, mul_smul]
    _ = c • n := by rw [@hN n ⟨_, hr⟩, zero_add, smul_assoc, hn]

omit [Fintype ι] [J.IsTwoSided] in
/-- In a module killed by `J`, `e j * a` acts as the scalar `c • e j` with
`e j * a ≡ c • e j` modulo `J`. -/
private theorem smul_smul_eq_smul_smul (hM : Module.IsTorsionBySet A M J) {a : A} {c : k}
    {j : ι} (hl : e j * a - c • e j ∈ J) (x : M) : e j • a • x = c • e j • x :=
  calc e j • a • x = (e j * a - c • e j) • x + (c • e j) • x := by
        rw [← add_smul, sub_add_cancel, mul_smul]
    _ = c • e j • x := by rw [@hM x ⟨_, hl⟩, zero_add, smul_assoc]

/-- **Maps into a vertex-`j` module.** Let the classes of a complete family of orthogonal
idempotents `e` span `A ⧸ J` over `k`, so that modules killed by `J` are modules over a product
of copies of `k`. If `J` kills `M` and `N`, and `e j` acts as the identity on `N`, then
restricting to the piece `e j M` identifies `A`-linear maps `M → N` with `k`-linear maps
`e j M → N`. The inverse sends `ψ` to `x ↦ ψ (e j • x)`. -/
noncomputable def linearMapEquivSMulTopLinearMap (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤)
    (hM : Module.IsTorsionBySet A M J) (hN : Module.IsTorsionBySet A N J) (j : ι)
    (hj : ∀ n : N, e j • n = n) :
    (M →ₗ[A] N) ≃ₗ[k] (↥(e j • (⊤ : Submodule k M)) →ₗ[k] N) where
  toFun φ := φ.restrictScalars k ∘ₗ (e j • (⊤ : Submodule k M)).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun ψ :=
    { toFun x := ψ ⟨e j • x, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top⟩
      map_add' x y := by
        rw [← map_add]
        exact congrArg ψ (Subtype.ext (smul_add _ _ _))
      map_smul' a x := by
        obtain ⟨c, hl, hr⟩ := he.exists_mul_sub_smul_mem hquot a j
        rw [RingHom.id_apply, smul_eq_smul_of_smul_eq_self hN hr (hj _), ← map_smul]
        exact congrArg ψ (Subtype.ext (smul_smul_eq_smul_smul hM hl x)) }
  left_inv φ := by
    ext x
    simp [hj]
  right_inv ψ := by
    ext ⟨x, hx⟩
    exact congrArg ψ (Subtype.ext ((he.idem j).mem_smul_top_iff_smul_eq_self.mp hx))

@[simp]
theorem linearMapEquivSMulTopLinearMap_apply (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤)
    (hM : Module.IsTorsionBySet A M J) (hN : Module.IsTorsionBySet A N J) (j : ι)
    (hj : ∀ n : N, e j • n = n) (φ : M →ₗ[A] N) (x : ↥(e j • (⊤ : Submodule k M))) :
    he.linearMapEquivSMulTopLinearMap hquot hM hN j hj φ x = φ x :=
  (rfl)

@[simp]
theorem linearMapEquivSMulTopLinearMap_symm_apply (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤)
    (hM : Module.IsTorsionBySet A M J) (hN : Module.IsTorsionBySet A N J) (j : ι)
    (hj : ∀ n : N, e j • n = n) (ψ : ↥(e j • (⊤ : Submodule k M)) →ₗ[k] N) (x : M) :
    (he.linearMapEquivSMulTopLinearMap hquot hM hN j hj).symm ψ x =
      ψ ⟨e j • x, Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top⟩ :=
  (rfl)

omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
/-- The idempotent `e j` acts as the identity on the top `A e j / J (A e j)`. -/
theorem smul_quotient_smul_top_eq_self (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤) (j : ι)
    (s : (Ideal.span {e j} : Ideal A) ⧸
      J • (⊤ : Submodule A (Ideal.span {e j} : Ideal A))) :
    e j • s = s := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp y.property
  obtain ⟨c, hl, hr⟩ := he.exists_mul_sub_smul_mem hquot a j
  have hmem : e j * a - a * e j ∈ J := by simpa using J.sub_mem hl hr
  have hy : e j • y - y = (e j * a - a * e j) • spanSingletonGenerator (e j) :=
    Subtype.ext (by simp [← ha, sub_mul, mul_assoc, (he.idem j).eq])
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub,
    Submodule.Quotient.mk_eq_zero, hy]
  exact Submodule.smul_mem_smul hmem Submodule.mem_top

end Hom

section Top

variable {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] {e : ι → A} {J : Ideal A} [J.IsTwoSided]

omit [Fintype ι] in
private theorem mk_spanSingletonGenerator_ne_zero {a : A} (ha : a ∉ J) :
    (Submodule.Quotient.mk (spanSingletonGenerator a) : (Ideal.span {a} : Ideal A) ⧸
      J • (⊤ : Submodule A (Ideal.span {a} : Ideal A))) ≠ 0 :=
  fun h ↦ ha (by simpa using coe_mem_of_mem_smul ((Submodule.Quotient.mk_eq_zero _).mp h))

omit [Fintype ι] [J.IsTwoSided] in
private theorem exists_smul_mk_spanSingletonGenerator_eq {a : A}
    (s : (Ideal.span {a} : Ideal A) ⧸ J • (⊤ : Submodule A (Ideal.span {a} : Ideal A))) :
    ∃ b : A, b • Submodule.Quotient.mk (spanSingletonGenerator a) = s := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  obtain ⟨b, rfl⟩ := exists_smul_spanSingletonGenerator y
  exact ⟨b, Submodule.Quotient.mk_smul _ _ _⟩

/-- A module killed by `J`, generated by a nonzero vector `n₀` fixed by `e j`, is the line
`k n₀`. -/
private noncomputable def equivOfSMulEqSelf {N : Type*} [AddCommGroup N] [Module A N]
    [instN : Module k N] [towerN : IsScalarTower k A N] (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤)
    (hN : Module.IsTorsionBySet A N J) (j : ι) (hj : ∀ n : N, e j • n = n) (n₀ : N)
    (hn₀ : n₀ ≠ 0) (hgen : ∀ n : N, ∃ a : A, a • n₀ = n) : k ≃ₗ[k] N :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton k N n₀)
    ⟨smul_left_injective k hn₀, fun n ↦ by
      obtain ⟨a, rfl⟩ := hgen n
      obtain ⟨c, -, hr⟩ := he.exists_mul_sub_smul_mem hquot a j
      exact ⟨c, (smul_eq_smul_of_smul_eq_self hN hr (hj n₀)).symm⟩⟩

/-- Maps from a module killed by `J` into a line generated by a vector fixed by `e j` are the
dual of the piece `e j M`. -/
private noncomputable def linearMapEquivDual {M N : Type*} [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [AddCommGroup N] [Module A N] [instN : Module k N]
    [towerN : IsScalarTower k A N] (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤)
    (hM : Module.IsTorsionBySet A M J) (hN : Module.IsTorsionBySet A N J) (j : ι)
    (hj : ∀ n : N, e j • n = n) (n₀ : N) (hn₀ : n₀ ≠ 0) (hgen : ∀ n : N, ∃ a : A, a • n₀ = n) :
    (M →ₗ[A] N) ≃ₗ[k] Module.Dual k ↥(e j • (⊤ : Submodule k M)) :=
  he.linearMapEquivSMulTopLinearMap hquot hM hN j hj ≪≫ₗ
    LinearEquiv.congrRight (he.equivOfSMulEqSelf hquot hN j hj n₀ hn₀ hgen).symm

/-- **The top of `A e j` is a line.** If the classes of the `e i` span `A ⧸ J` over `k` and
`e j ∉ J`, then `c ↦ c • [e j]` identifies `k` with the top `A e j / J (A e j)`. -/
noncomputable def equivQuotientSMulTop (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤) (j : ι)
    (hj : e j ∉ J) :
    k ≃ₗ[k] (Ideal.span {e j} : Ideal A) ⧸
      J • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)) :=
  he.equivOfSMulEqSelf hquot (Module.isTorsionBySet_quotient_ideal_smul _ J) j
    (he.smul_quotient_smul_top_eq_self hquot j) _ (mk_spanSingletonGenerator_ne_zero hj)
    exists_smul_mk_spanSingletonGenerator_eq

@[simp]
theorem equivQuotientSMulTop_apply (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤) (j : ι)
    (hj : e j ∉ J) (c : k) :
    he.equivQuotientSMulTop hquot j hj c =
      c • Submodule.Quotient.mk (spanSingletonGenerator (e j)) :=
  (rfl)

/-- The top `A e j / J (A e j)` is one-dimensional over `k`. -/
theorem finrank_quotient_smul_top (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤) (j : ι)
    (hj : e j ∉ J) :
    Module.finrank k ((Ideal.span {e j} : Ideal A) ⧸
      J • (⊤ : Submodule A (Ideal.span {e j} : Ideal A))) = 1 := by
  rw [← (he.equivQuotientSMulTop hquot j hj).finrank_eq, Module.finrank_self]

/-- The top `A e j / J (A e j)` is a simple `A`-module. -/
theorem isSimpleModule_quotient_smul_top (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤) (j : ι)
    (hj : e j ∉ J) :
    IsSimpleModule A ((Ideal.span {e j} : Ideal A) ⧸
      J • (⊤ : Submodule A (Ideal.span {e j} : Ideal A))) := by
  set σ := he.equivQuotientSMulTop hquot j hj
  have := σ.symm.nontrivial
  refine isSimpleModule_iff_toSpanSingleton_surjective.mpr ⟨inferInstance, fun s hs t ↦ ?_⟩
  obtain ⟨c, rfl⟩ := σ.surjective s
  obtain ⟨d, rfl⟩ := σ.surjective t
  have hc : c ≠ 0 := by rintro rfl; exact hs (map_zero σ)
  refine ⟨algebraMap k A (d / c), ?_⟩
  rw [LinearMap.toSpanSingleton_apply, algebraMap_smul, ← map_smul, smul_eq_mul,
    div_mul_cancel₀ d hc]

end Top

section Ext

open scoped ModuleCat.Algebra

universe u

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] {e : ι → A}

/-- **Extensions between simple tops are the duals of the radical-layer corners.** Let `e` be
a complete family of orthogonal idempotents of a `k`-algebra `A` whose classes span `A ⧸ J`,
where `J` is the Jacobson radical, and write `Sᵢ = A eᵢ / J (A eᵢ)`. For `e j ≠ 0`,

`Ext¹_A(Sᵢ, Sⱼ) ≃ₗ[k] Homₖ(eⱼ (J / J²) eᵢ, k)`.

This is the linear algebra behind reading the arrows `i → j` of the quiver of a basic algebra
as `dimₖ Ext¹_A(Sᵢ, Sⱼ)`. -/
noncomputable def extQuotientSMulTopEquivDual (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k
      (Set.range fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e i)) = ⊤)
    (i j : ι) (hj : e j ≠ 0) :
    Ext (ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e i} : Ideal A))))
      (ModuleCat.of A ((Ideal.span {e j} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)))) 1 ≃ₗ[k]
      Module.Dual k (radicalLayerCorner k (Ring.jacobson A) (e j) (e i)) := by
  have hjJ : e j ∉ Ring.jacobson A := fun h ↦
    hj ((he.idem j).eq_zero_of_mem_jacobson_bot (Ideal.jacobson_bot (R := A) ▸ h))
  have := (he.idem i).projective_span_singleton
  have := he.isSimpleModule_quotient_smul_top hquot j hjJ
  let P := ModuleCat.of A (Ideal.span {e i} : Ideal A)
  let S := ModuleCat.of A ((Ideal.span {e j} : Ideal A) ⧸
    Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)))
  -- `Ext` is a `k`-module through the `k`-module structure that `ModuleCat` puts on `S`, which
  -- is not definitionally the quotient-module structure; pass the former explicitly.
  exact (Submodule.radicalLayerHomEquivExt.{u, u, u} (k := k) (P := P)
      (Ring.jacobson A • (⊤ : Submodule A P)) (Ring.jacobson_smul_top_le A P) S).symm ≪≫ₗ
    he.linearMapEquivDual (N := S) (instN := ModuleCat.Algebra.instModuleCarrier)
      (towerN := ModuleCat.Algebra.instIsScalarTowerCarrier) hquot
      (Module.isTorsionBySet_quotient_ideal_smul _ _)
      (Module.isTorsionBySet_quotient_ideal_smul _ _) j (he.smul_quotient_smul_top_eq_self hquot j)
      _ (mk_spanSingletonGenerator_ne_zero hjJ) exists_smul_mk_spanSingletonGenerator_eq ≪≫ₗ
    ((he.idem j).smulTopRadicalLayerEquiv (he.idem i)).symm.dualMap

/-- **The arrow count of the Ext-quiver.** Under the hypotheses of
`CompleteOrthogonalIdempotents.extQuotientSMulTopEquivDual`, `dimₖ Ext¹_A(Sᵢ, Sⱼ)` is the
dimension of the corner `eⱼ (J / J²) eᵢ` of the first radical layer. -/
theorem finrank_ext_quotient_smul_top (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k
      (Set.range fun i ↦ Ideal.Quotient.mk (Ring.jacobson A) (e i)) = ⊤)
    (i j : ι) (hj : e j ≠ 0) :
    Module.finrank k (Ext (ModuleCat.of A ((Ideal.span {e i} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e i} : Ideal A))))
      (ModuleCat.of A ((Ideal.span {e j} : Ideal A) ⧸
        Ring.jacobson A • (⊤ : Submodule A (Ideal.span {e j} : Ideal A)))) 1) =
      Module.finrank k (radicalLayerCorner k (Ring.jacobson A) (e j) (e i)) := by
  rw [(he.extQuotientSMulTopEquivDual hquot i j hj).finrank_eq, Subspace.dual_finrank_eq]

end Ext

end CompleteOrthogonalIdempotents
