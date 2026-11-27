/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import TauCeti.GroupTheory.Coset.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Coset bases of group algebras

An injective group homomorphism `p : M →* N` makes `R[N]` free as a left `R[M]`-module, with
scalars acting through `mapDomainRingHom R p`. The basis consists of the inverses of chosen
left-coset representatives of `p.range`, which represent its right cosets.

## Main definitions and results

* `TauCeti.MonoidAlgebra.basisCosets`: the coset basis of `R[N]` over `R[M]`.
* `TauCeti.MonoidAlgebra.coeff_basisCosets_repr`: evaluates arbitrary `m : M` coefficients of the
  `q`-th coordinate in `basisCosets`.
* `TauCeti.MonoidAlgebra.bijective_mapDomain_add_mapDomain_mul_single`: when `p.range` has the
  two right cosets `p.range` and `p.range * g`, every element of `R[N]` is uniquely
  `p(a) + p(b) * g`.
* `Subgroup.restrictSubgroup_compHom_finite_projective` and
  `Subgroup.restrictSubgroup_compHom_isScalarTower_finite_projective`: restricting a finitely
  generated projective `R[G]`-module to the group algebra of a finite-index subgroup along the
  canonical `RingHom.toModule` and `Module.compHom` actions keeps it finitely generated and
  projective, with the corresponding scalar towers.
* `TauCeti.MonoidAlgebra.subsingleton_of_infinite_quotient` and
  `TauCeti.MonoidAlgebra.subsingleton_of_infinite_group`: a finite projective `R[G]`-module that
  is finitely generated over an infinite-index subgroup algebra `R[H]` (or over `R` when `G` is
  infinite) is trivial.
-/

public section

noncomputable section

open MonoidAlgebra

namespace TauCeti.MonoidAlgebra

variable {R M N : Type*} [Semiring R] [Group M] [Group N]

/-- Regroup coefficients using `(q, m) ↦ p m * q.out⁻¹`, obtained by inverting the usual
left-coset decomposition. -/
private def cosetAddEquiv (p : M →* N) (hp : Function.Injective p) :
    ((N ⧸ p.range) →₀ R[M]) ≃+ R[N] :=
  (Finsupp.mapRange.addEquiv coeffAddEquiv).trans <|
    Finsupp.curryAddEquiv.symm.trans <|
      (Finsupp.domCongr ((Equiv.prodCongr (Equiv.refl _)
        ((Equiv.inv M).trans (MonoidHom.ofInjective hp).toEquiv)).trans
          (Subgroup.groupEquivQuotientProdSubgroup.symm.trans (Equiv.inv N)))).trans
            coeffAddEquiv.symm

private theorem cosetAddEquiv_single_single (p : M →* N) (hp : Function.Injective p)
    (q : N ⧸ p.range) (m : M) (r : R) :
    cosetAddEquiv p hp (Finsupp.single q (single m r)) = single (p m * q.out⁻¹) r := by
  simp [cosetAddEquiv, Finsupp.curryAddEquiv, Finsupp.curryEquiv,
    Subgroup.groupEquivQuotientProdSubgroup_symm_apply, MonoidHom.ofInjective_apply]

private theorem cosetAddEquiv_single (p : M →* N) (hp : Function.Injective p)
    (q : N ⧸ p.range) (a : R[M]) :
    cosetAddEquiv p hp (Finsupp.single q a) = mapDomain p a * single q.out⁻¹ 1 := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp [Finsupp.single_add, ha, hb, mapDomain_add, add_mul]
  | single m r => simp [cosetAddEquiv_single_single, single_mul_single]

/-- The coset decomposition is linear for the source group-algebra action. -/
private def cosetLinearEquiv (p : M →* N) (hp : Function.Injective p) :
    letI := (mapDomainRingHom R p).toModule
    ((N ⧸ p.range) →₀ R[M]) ≃ₗ[R[M]] R[N] := by
  letI := (mapDomainRingHom R p).toModule
  refine { cosetAddEquiv p hp with map_smul' := ?_ }
  intro a x
  simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | single q b =>
    rw [Finsupp.smul_single, smul_eq_mul, cosetAddEquiv_single, cosetAddEquiv_single,
      RingHom.toModule_smul]
    simp [mapDomainRingHom_apply, mapDomain_mul, mul_assoc]

variable (R)

/-- Inverses of left-coset representatives form a basis of the target group algebra over the
source of an injective group-algebra map. These inverses represent the right cosets, as required
for the left scalar action through `mapDomainRingHom R p`. -/
def basisCosets (p : M →* N) (hp : Function.Injective p) :
    letI := (mapDomainRingHom R p).toModule
    Module.Basis (N ⧸ p.range) R[M] R[N] := by
  letI := (mapDomainRingHom R p).toModule
  exact ⟨(cosetLinearEquiv p hp).symm⟩

/-- The coset basis vector is the monomial at the inverse of the chosen representative. -/
@[simp]
theorem basisCosets_apply (p : M →* N) (hp : Function.Injective p) (q : N ⧸ p.range) :
    basisCosets R p hp q = single q.out⁻¹ (1 : R) := by
  simp [basisCosets, Module.Basis.coe_ofRepr, cosetLinearEquiv, cosetAddEquiv_single]

/-- In `basisCosets R p hp`, the `R[M]`-coordinates of `single (p m * q.out⁻¹) r` are supported at
`q` with value `single m r`. -/
@[simp]
theorem basisCosets_repr_single (p : M →* N) (hp : Function.Injective p)
    (q : N ⧸ p.range) (m : M) (r : R) :
    letI := (mapDomainRingHom R p).toModule
    (basisCosets R p hp).repr (single (p m * q.out⁻¹) r) = Finsupp.single q (single m r) := by
  let _ := (mapDomainRingHom R p).toModule
  have h : single (p m * q.out⁻¹) r = (single m r : R[M]) • basisCosets R p hp q := by
    rw [basisCosets_apply, RingHom.toModule_smul, mapDomainRingHom_apply, mapDomain_single,
      single_mul_single, mul_one]
  rw [h, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- In `basisCosets R p hp`, the `m`-th coefficient of the `q`-th `R[M]`-coordinate of `x : R[N]`
is `x.coeff (p m * q.out⁻¹)`. -/
@[simp]
theorem coeff_basisCosets_repr (p : M →* N) (hp : Function.Injective p) (x : R[N])
    (q : N ⧸ p.range) (m : M) :
    letI := (mapDomainRingHom R p).toModule
    ((basisCosets R p hp).repr x q).coeff m = x.coeff (p m * q.out⁻¹) := by
  let _ := (mapDomainRingHom R p).toModule
  induction x using induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single n r =>
    let q' : N ⧸ p.range := QuotientGroup.mk n⁻¹
    obtain ⟨m', hm'⟩ := QuotientGroup.eq.1 (QuotientGroup.out_eq' q').symm
    have hn : n = p m' * q'.out⁻¹ := eq_mul_inv_of_mul_eq (by simpa using hm'.symm)
    rw [hn, basisCosets_repr_single]
    by_cases hq : q' = q
    · subst hq
      by_cases hm : m' = m
      · subst hm; simp
      · simp [coeff_single, hm, hp.ne hm]
    · have hne : p m' * q'.out⁻¹ ≠ p m * q.out⁻¹ := fun heq ↦ hq <| by
        have hmem : q.out⁻¹ * q'.out ∈ p.range := ⟨m⁻¹ * m', by
          rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc]
          have h1 : p m * q.out⁻¹ * q'.out = p m' := by
            rw [← heq, mul_assoc, inv_mul_cancel, mul_one]
          exact h1.symm⟩
        rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
        exact (QuotientGroup.eq.2 hmem).symm
      simp [Ne.symm hq, coeff_single, hne]

/-- Every coset `H g⁻¹` arising from the support of `f x`, for `x` in the `R[H]`-span of `s`,
already appears in the finite set of cosets coming from the generators `m ∈ s`. -/
private theorem quotient_inv_mem_biUnion_support_of_mem_span {G : Type*} [Group G]
    (H : Subgroup G) [DecidableEq (G ⧸ H)] {P : Type*} [AddCommMonoid P] [Module R[G] P]
    [Module R[H] P] (hP : ∀ (r : R[H]) (p : P), r • p = mapDomainRingHom R H.subtype r • p)
    (f : P →ₗ[R[G]] R[G]) (s : Finset P) {x : P} (hx : x ∈ Submodule.span R[H] (s : Set P))
    {g : G} (hg : g ∈ (f x).coeff.support) :
    (QuotientGroup.mk g⁻¹ : G ⧸ H) ∈
      s.biUnion fun m ↦ (f m).coeff.support.image fun g₀ ↦ QuotientGroup.mk g₀⁻¹ := by
  classical
  induction hx using Submodule.span_induction generalizing g with
  | mem m hm => exact Finset.mem_biUnion.2 ⟨m, hm, Finset.mem_image_of_mem _ hg⟩
  | zero => simp at hg
  | add x y _ _ hx hy =>
    rw [map_add, coeff_add] at hg
    exact (Finset.mem_union.1 (Finsupp.support_add hg)).elim (hx ·) (hy ·)
  | smul c x _ hx =>
    induction c using induction_linear generalizing g with
    | zero => simp at hg
    | add c₁ c₂ hc₁ hc₂ =>
      rw [add_smul, map_add, coeff_add] at hg
      exact (Finset.mem_union.1 (Finsupp.support_add hg)).elim (hc₁ ·) (hc₂ ·)
    | single h a =>
      have himg : f (single h a • x) = single (h : G) a * f x := by
        rw [hP, map_smul]; simp [smul_eq_mul]
      rw [himg, Finsupp.mem_support_iff, coeff_single_mul_apply] at hg
      have hq : (QuotientGroup.mk g⁻¹ : G ⧸ H) = QuotientGroup.mk ((h : G)⁻¹ * g)⁻¹ :=
        QuotientGroup.eq.2 (by simp)
      exact hq ▸ hx (Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hg))

/-- If `G ⧸ H` is infinite, any finite projective `R[G]`-module that is finitely generated over
`R[H]` is trivial. -/
theorem subsingleton_of_infinite_quotient {G : Type*} [Group G] (H : Subgroup G)
    [Infinite (G ⧸ H)] (P : Type*) [AddCommMonoid P] [Module R[G] P] [Module R[H] P]
    [Module.Finite R[G] P] [Module.Projective R[G] P] [Module.Finite R[H] P]
    (hP : ∀ (r : R[H]) (p : P), r • p = mapDomainRingHom R H.subtype r • p) :
    Subsingleton P := by
  classical
  obtain ⟨r, π, i, -, -, hπi⟩ := Module.Finite.exists_comp_eq_id_of_projective R[G] P
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R[H]) (M := P)
  refine (subsingleton_iff_forall_eq 0).2 fun p ↦ ?_
  -- The `R[H]`-generators bound the right-coset support of `i x k` to a finite set `S`;
  -- translating `p` by `q.out⁻¹ * g₁⁻¹` moves `g₁` to a coset `q ∉ S`, a contradiction.
  have hip : i p = 0 := by
    funext k; by_contra hne
    obtain ⟨g₁, hg₁⟩ := Finsupp.support_nonempty_iff.2 (coeff_eq_zero.not.2 hne)
    let ik : P →ₗ[R[G]] R[G] := (LinearMap.proj k).comp i
    let S : Finset (G ⧸ H) :=
      s.biUnion fun m ↦ (ik m).coeff.support.image fun g₀ ↦ QuotientGroup.mk g₀⁻¹
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset S
    have ht : q.out⁻¹ * g₁⁻¹ * g₁ ∈ (ik (single (q.out⁻¹ * g₁⁻¹) (1 : R) • p)).coeff.support := by
      rw [LinearMap.comp_apply, LinearMap.proj_apply, map_smul, Pi.smul_apply, smul_eq_mul,
        Finsupp.mem_support_iff, coeff_single_mul_apply, inv_mul_cancel_left, one_mul]
      exact Finsupp.mem_support_iff.1 hg₁
    have hx : single (q.out⁻¹ * g₁⁻¹) (1 : R) • p ∈ Submodule.span R[H] (s : Set P) :=
      hs.symm ▸ Submodule.mem_top
    exact hq ((by simp : (QuotientGroup.mk (q.out⁻¹ * g₁⁻¹ * g₁)⁻¹ : G ⧸ H) = q) ▸
      quotient_inv_mem_biUnion_support_of_mem_span R H hP ik s hx ht)
  simpa [hip] using (LinearMap.congr_fun hπi p).symm

/-- If `G` is infinite, any finite projective `R[G]`-module that is finitely generated over `R` is
trivial. -/
theorem subsingleton_of_infinite_group (G : Type*) [Group G] [Infinite G]
    (P : Type*) [AddCommMonoid P] [Module R P] [Module R[G] P] [IsScalarTower R R[G] P]
    [Module.Finite R[G] P] [Module.Projective R[G] P] [Module.Finite R P] :
    Subsingleton P := by
  let H : Subgroup G := ⊥
  let _ : Module R[H] P := Module.compHom P (mapDomainRingHom R H.subtype)
  have : Infinite (G ⧸ H) :=
    Infinite.of_injective _ (QuotientGroup.quotientBot (G := G)).symm.injective
  have : IsScalarTower R R[H] P := ⟨fun c r p ↦
    (congrArg (· • p) (mapDomain_smul H.subtype c r)).trans (smul_assoc c _ p)⟩
  have : Module.Finite R[H] P := Module.Finite.of_restrictScalars_finite R R[H] P
  exact subsingleton_of_infinite_quotient R H P fun _ _ ↦ rfl

variable {R}

/-- **A group algebra over a subgroup with two right cosets.** Let `p : M →* N` be injective and
let `g ∉ p.range` be such that every element of `N` lies in `p.range` or in `p.range * g`, so that
these are the two right cosets of `p.range`. Then every element of `R[N]` is uniquely
`p(a) + p(b) * g` with `a, b ∈ R[M]`: as a module over `R[M]` through `mapDomain p`, `R[N]` is
free with basis `1, g`. -/
theorem bijective_mapDomain_add_mapDomain_mul_single (p : M →* N) (hp : Function.Injective p)
    {g : N} (hg : g ∉ p.range) (h : ∀ x, x ∈ p.range ∨ x * g⁻¹ ∈ p.range) :
    Function.Bijective fun ab : R[M] × R[M] ↦
      mapDomain p ab.1 + mapDomain p ab.2 * single g (1 : R) := by
  -- The coefficients at `p m` and `p m * g` read off the two components.
  have h₁ (a b : R[M]) (m : M) :
      (mapDomain p a + mapDomain p b * single g (1 : R)).coeff (p m) = a.coeff m := by
    have : p m * g⁻¹ ∉ Set.range p := by
      rintro ⟨k, hk⟩
      exact hg ⟨k⁻¹ * m, by simp [hk]⟩
    simp [coeff_mul_single_apply, Finsupp.mapDomain_apply_of_injective hp,
      Finsupp.mapDomain_of_notMem_range _ _ this]
  have h₂ (a b : R[M]) (m : M) :
      (mapDomain p a + mapDomain p b * single g (1 : R)).coeff (p m * g) = b.coeff m := by
    have : p m * g ∉ Set.range p := by
      rintro ⟨k, hk⟩
      exact hg ⟨m⁻¹ * k, by simp [hk]⟩
    simp [coeff_mul_single_apply, Finsupp.mapDomain_apply_of_injective hp,
      Finsupp.mapDomain_of_notMem_range _ _ this]
  refine ⟨fun ⟨a, b⟩ ⟨a', b'⟩ hab ↦ ?_, fun u ↦ ?_⟩
  · have hc (x : N) := congrArg (fun v : R[N] ↦ v.coeff x) hab
    refine Prod.ext (coeff_injective (Finsupp.ext fun m ↦ ?_))
      (coeff_injective (Finsupp.ext fun m ↦ ?_))
    · simpa only [h₁] using hc (p m)
    · simpa only [h₂] using hc (p m * g)
  · refine ⟨(ofCoeff (u.coeff.comapDomain p hp.injOn),
      ofCoeff (u.coeff.comapDomain (fun m ↦ p m * g) ((mul_left_injective g).comp hp).injOn)), ?_⟩
    refine coeff_injective (Finsupp.ext fun x ↦ ?_)
    rcases h x with ⟨m, rfl⟩ | ⟨m, hm⟩
    · rw [h₁]
      simp
    · obtain rfl : x = p m * g := by rw [hm, inv_mul_cancel_right]
      rw [h₂]
      simp

end TauCeti.MonoidAlgebra

namespace MonoidAlgebra

variable {R : Type*} [Semiring R] {G : Type*} [Group G]

/-- Restricting a finitely generated projective `R[G]`-module `X` to the group algebra of a
finite-index subgroup `C` along the canonical `RingHom.toModule` and `Module.compHom` actions
gives a finitely generated projective `R[C]`-module, with compatible `R[C]`-`R[G]` scalar towers. -/
theorem _root_.Subgroup.restrictSubgroup_compHom_finite_projective (C : Subgroup G)
    [C.FiniteIndex] (X : Type*) [AddCommMonoid X] [Module R[G] X]
    [Module.Finite R[G] X] [Module.Projective R[G] X] :
    letI : Module R[C] R[G] := (mapDomainRingHom R C.subtype).toModule
    letI : Module R[C] X := Module.compHom X (mapDomainRingHom R C.subtype)
    IsScalarTower R[C] R[G] R[G] ∧ IsScalarTower R[C] R[G] X ∧
      Module.Finite R[C] X ∧ Module.Projective R[C] X := by
  let φ : R[C] →+* R[G] := mapDomainRingHom R C.subtype
  let _ : Module R[C] R[G] := φ.toModule
  let _ : Module R[C] X := Module.compHom X φ
  have hAA : IsScalarTower R[C] R[G] R[G] := ⟨fun r s t ↦ mul_assoc (φ r) s t⟩
  let b := TauCeti.MonoidAlgebra.basisCosets R C.subtype C.subtype_injective
  have : Finite (G ⧸ C.subtype.range) := by rw [Subgroup.range_subtype]; infer_instance
  have : Module.Free R[C] R[G] := .of_basis b
  have : Module.Finite R[C] R[G] := .of_basis b
  have hAX : IsScalarTower R[C] R[G] X := ⟨fun r s x ↦ mul_smul (φ r) s x⟩
  exact ⟨hAA, hAX, .trans R[G] X, .trans R[C] R[G] X⟩

/-- Restricting a finitely generated projective `R[G]`-module `X` to the group algebra of a
finite-index subgroup `C` along the canonical `RingHom.toModule` and `Module.compHom` actions
gives a finitely generated projective `R[C]`-module on which `R` and `R[G]` act compatibly. -/
theorem _root_.Subgroup.restrictSubgroup_compHom_isScalarTower_finite_projective (C : Subgroup G)
    [C.FiniteIndex] (X : Type*) [AddCommMonoid X] [Module R X] [Module R[G] X]
    [IsScalarTower R R[G] X] [Module.Finite R[G] X] [Module.Projective R[G] X] :
    letI : Module R[C] R[G] := (mapDomainRingHom R C.subtype).toModule
    letI : Module R[C] X := Module.compHom X (mapDomainRingHom R C.subtype)
    IsScalarTower R[C] R[G] R[G] ∧ IsScalarTower R[C] R[G] X ∧ IsScalarTower R R[C] X ∧
      Module.Finite R[C] X ∧ Module.Projective R[C] X := by
  let _ : Module R[C] R[G] := (mapDomainRingHom R C.subtype).toModule
  let _ : Module R[C] X := Module.compHom X (mapDomainRingHom R C.subtype)
  obtain ⟨hAA, hAX, hfin, hproj⟩ := C.restrictSubgroup_compHom_finite_projective (R := R) X
  refine ⟨hAA, hAX, ⟨fun a r x ↦ ?_⟩, hfin, hproj⟩
  exact (congrArg (· • x) (mapDomain_smul C.subtype a r)).trans (smul_assoc a _ x)

end MonoidAlgebra
