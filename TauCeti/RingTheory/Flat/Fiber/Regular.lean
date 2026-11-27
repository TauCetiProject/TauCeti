/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Flat
import TauCeti.Algebra.Regular.SMul
import TauCeti.RingTheory.Flat.QuotSMulTop
import TauCeti.RingTheory.Flat.QuotientRegular
import TauCeti.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import TauCeti.RingTheory.Flat.Localization
import TauCeti.RingTheory.Flat.Locus
import TauCeti.RingTheory.Flat.TensorProduct
import TauCeti.RingTheory.Localization.Module.TensorProduct
import TauCeti.RingTheory.Localization.Away.Basic
import TauCeti.RingTheory.Support.Basic

/-!
# Fibrewise regularity and flat principal quotients

Let `B` be a noetherian flat algebra over a noetherian ring `A`, let `R` be any `A`-algebra and
let `b ∈ B`. If `1 ⊗ (1 ⊗ b)` is a nonzerodivisor on the fibre ring `κ(p) ⊗[R] (R ⊗[A] B)` for
every prime `p` of `R`, then `1 ⊗ b` is a nonzerodivisor on `R ⊗[A] B`
(`Module.Flat.isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber`). Neither `R` nor `R ⊗[A] B`
need be noetherian. This is the local algebra behind the fibre criterion for relative effective
Cartier divisors. `TauCeti.RingTheory.Flat.Fiber.FinitePresentation` applies these results to
noetherian models of flat finitely presented algebras.

1. Let `q` be a prime of `R ⊗[A] B`, lying over the prime `p` of `R`, the prime `r` of `B` and
   the prime `p₀` of `A`. The fibre ring `κ(p₀) ⊗[A] B` embeds into `κ(p) ⊗[R] (R ⊗[A] B)`,
   by extension of residue fields (`Module.Flat.isSMulRegular_fiber_comap`). So `b` is a
   nonzerodivisor on it.
2. By the local criterion over the noetherian local ring `A_{p₀}`, `b` is a nonzerodivisor on
   `B_r` and `B_r ⧸ (b)` is flat over `A`
   (`Module.Flat.isSMulRegular_localization_of_isSMulRegular_fiber`).
3. Hence `1 ⊗ b` stays a nonzerodivisor on `R ⊗[A] B_r`, the localization of `R ⊗[A] B` at the
   image of `B ∖ r`. An element killed by `1 ⊗ b` is therefore killed by some `1 ⊗ s` with
   `s ∉ r`, which lies outside `q`. Its annihilator lies in no prime, so the element is zero.

## Main results

* `Module.Flat.isSMulRegular_fiber_comap`: for `A`-algebras `B` and `R`,
  regularity of `1 ⊗ (1 ⊗ b)` on a fibre ring of `R ⊗[A] B` over `R` gives regularity of `1 ⊗ b`
  on the fibre ring of `B` over the prime below.
* `Module.Flat.isSMulRegular_localization_of_isSMulRegular_fiber`: for a noetherian flat algebra
  `B` over a noetherian ring `A`, an element which is a nonzerodivisor on the fibre ring over a
  prime `p` of `A` is a nonzerodivisor on `B_r` for every prime `r` over `p`, with `B_r ⧸ (b)`
  flat over `A`.
* `Module.Flat.isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber`: the statement above.

* `Ideal.isSMulRegular_fiber_baseChange`: fibrewise regularity persists under base change.
* `Ideal.exists_notMem_forall_pow_smul_eq_zero`: at a flat fibre point, one denominator
  annihilates every tensor kernel by powers.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 22.5 and its Corollary.
-/

public section

open TensorProduct Algebra.TensorProduct
open scoped Pointwise

variable {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]

namespace Module.Flat

/-- Let `B` and `R` be `A`-algebras and `p` a prime of `R`, lying over the prime
`p₀` of `A`. If `1 ⊗ (1 ⊗ b)` is a nonzerodivisor on the fibre ring `κ(p) ⊗[R] (R ⊗[A] B)`, then
`1 ⊗ b` is a nonzerodivisor on `κ(p₀) ⊗[A] B`, which embeds into it. -/
theorem isSMulRegular_fiber_comap (p : Ideal R) [p.IsPrime] {b : B}
    (h : IsSMulRegular (p.Fiber (R ⊗[A] B)) ((1 : p.ResidueField) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] b))) :
    IsSMulRegular ((p.comap (algebraMap A R)).Fiber B)
      ((1 : (p.comap (algebraMap A R)).ResidueField) ⊗ₜ[A] b) := by
  let p₀ := p.comap (algebraMap A R)
  let ι : p₀.ResidueField →ₐ[A] p.ResidueField :=
    Ideal.ResidueField.mapₐ p₀ p (Algebra.ofId A R) rfl
  let := ι.toRingHom.toAlgebra
  have : IsScalarTower A p₀.ResidueField p.ResidueField :=
    .of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  -- The comparison factors through extension of scalars along `κ(p₀) → κ(p)`.
  let φ : p₀.Fiber B →ₐ[A] p.Fiber (R ⊗[A] B) :=
    ((cancelBaseChange A R p.ResidueField p.ResidueField B).symm.toAlgHom.restrictScalars A).comp
      (map ι (AlgHom.id A B))
  have hφ : Function.Injective φ := by
    have hmap : Function.Injective (map ι (AlgHom.id A B)) := by
      let e := cancelBaseChange A p₀.ResidueField p.ResidueField p.ResidueField B
      have heq : map ι (AlgHom.id A B) =
          (e.toAlgHom.restrictScalars A).comp
            (includeRight.restrictScalars A) := by
        ext; simp [e]
      rw [heq]
      exact e.injective.comp (includeRight_injective (RingHom.injective _))
    exact (cancelBaseChange A R p.ResidueField p.ResidueField B).symm.injective.comp hmap
  have hb : φ ((1 : p₀.ResidueField) ⊗ₜ[A] b) = (1 : p.ResidueField) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] b) := by
    simp [φ]
  intro x y hxy
  refine hφ (h ?_)
  simp only [smul_eq_mul] at hxy ⊢
  rw [← hb, ← map_mul, ← map_mul, hxy]

/-- A regular equation on the closed fibre of a flat local algebra is regular,
with flat quotient. -/
theorem isSMulRegular_and_flat_quotient_localization [IsNoetherianRing A]
    [IsNoetherianRing B] (q : Ideal B) [q.IsPrime]
    [Flat A (Localization.AtPrime q)] (b : B)
    (h : IsSMulRegular (Localization.AtPrime q ⧸
      (q.comap (algebraMap A B)).map (algebraMap A (Localization.AtPrime q)))
      (algebraMap B (Localization.AtPrime q) b)) :
    IsSMulRegular (Localization.AtPrime q) (algebraMap B (Localization.AtPrime q) b) ∧
      Flat A (Localization.AtPrime q ⧸
        Ideal.span {algebraMap B (Localization.AtPrime q) b}) := by
  let p := q.comap (algebraMap A B)
  let Rp := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let φ : Rp →+* Bq := Localization.localRingHom p q (algebraMap A B) rfl
  let : Algebra Rp Bq := φ.toAlgebra
  have : IsScalarTower A Rp Bq := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B Bq]
    exact (Localization.localRingHom_to_map p q (algebraMap A B) rfl a).symm
  have : IsLocalHom (algebraMap Rp Bq) :=
    Localization.isLocalHom_localRingHom p q (algebraMap A B) rfl
  have : Flat Rp Bq := (Module.flat_iff_of_isLocalization Rp p.primeCompl Bq).mpr
    inferInstance
  have hmax : ((IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Bq) • ⊤ : Submodule Bq Bq) =
      p.map (algebraMap A Bq) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, smul_eq_mul, Ideal.mul_top]
  have hfib : IsSMulRegular (Bq ⧸ ((IsLocalRing.maximalIdeal Rp).map (algebraMap Rp Bq) • ⊤ :
      Submodule Bq Bq)) (algebraMap B Bq b) := by
    rw [hmax]
    exact h
  refine ⟨isSMulRegular_of_isSMulRegular_quotient hfib, ?_⟩
  have := quotSMulTop_of_isSMulRegular_quotient hfib
  have : Flat A (QuotSMulTop (algebraMap B Bq b) Bq) := .trans A Rp _
  exact .of_linearEquiv ((Submodule.quotEquivOfEq (Ideal.span {algebraMap B Bq b})
    (algebraMap B Bq b • ⊤ : Submodule Bq Bq) (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])).restrictScalars A)

/-- **A nonzerodivisor on a fibre ring is a nonzerodivisor nearby.** Let `A` and `B` be noetherian
with `B` flat over `A`, and let `r` be a prime of `B` over the prime `p` of `A`. If `1 ⊗ b` is a
nonzerodivisor on the fibre ring `κ(p) ⊗[A] B`, then `b` is a nonzerodivisor on `B_r` and
`B_r ⧸ (b)` is flat over `A`. -/
theorem isSMulRegular_localization_of_isSMulRegular_fiber [IsNoetherianRing A]
    [IsNoetherianRing B] [Flat A B] (p : Ideal A) [p.IsPrime] {b : B}
    (hb : IsSMulRegular (p.Fiber B) ((1 : p.ResidueField) ⊗ₜ[A] b)) (r : Ideal B) [r.IsPrime]
    (hr : r.comap (algebraMap A B) = p) :
    IsSMulRegular (Localization.AtPrime r) (algebraMap B (Localization.AtPrime r) b) ∧
      Flat A (Localization.AtPrime r ⧸
        Ideal.span {algebraMap B (Localization.AtPrime r) b}) := by
  -- The prime `Q` of the fibre ring over `r`.
  obtain ⟨Q, _, rfl⟩ : ∃ Q : Ideal (p.Fiber B), Q.IsPrime ∧ Q.comap includeRight = r := by
    let e := PrimeSpectrum.preimageEquivFiber A B ⟨p, ‹_›⟩
    refine ⟨(e ⟨⟨r, ‹_›⟩, PrimeSpectrum.ext hr⟩).asIdeal, inferInstance, ?_⟩
    have := congrArg Subtype.val (e.symm_apply_apply ⟨⟨r, ‹_›⟩, PrimeSpectrum.ext hr⟩)
    rwa [PrimeSpectrum.preimageEquivFiber_symm_apply_coe, PrimeSpectrum.ext_iff,
      PrimeSpectrum.comap_asIdeal] at this
  set r := Q.comap (includeRight : B →ₐ[A] p.Fiber B)
  let Br := Localization.AtPrime r
  let := Localization.AtPrime.algebraOfLiesOver p r
  -- `b` is a nonzerodivisor on the closed fibre `B_r ⧸ p B_r ≃ (κ(p) ⊗[A] B)_Q`.
  have hloc : IsSMulRegular (Localization.AtPrime Q)
      (algebraMap (p.Fiber B) _ ((1 : p.ResidueField) ⊗ₜ[A] b)) := hb.of_flat
  let e := (Ideal.Fiber.localizationAlgEquivQuotient p Q).toRingEquiv
  have he : e (algebraMap (p.Fiber B) _ ((1 : p.ResidueField) ⊗ₜ[A] b)) =
      Ideal.Quotient.mk _ (algebraMap B Br b) := by
    simp [e, Br, r, Ideal.Fiber.localizationAlgEquivQuotient, ← Ideal.Quotient.mk_algebraMap]
  apply isSMulRegular_and_flat_quotient_localization r b
  rw [hr, ← isSMulRegular_algebraMap_iff (A := Br ⧸ p.map (algebraMap A Br)),
    Ideal.Quotient.algebraMap_eq, ← he]
  exact (TauCeti.isSMulRegular_map_iff e _).mpr hloc

/-- **Nonzerodivisors on the fibres of a base change of a noetherian flat algebra.** Let `B` be a
noetherian flat algebra over a noetherian ring `A`, let `R` be any `A`-algebra, and let `b ∈ B`.
If `1 ⊗ (1 ⊗ b)` is a nonzerodivisor on the fibre ring `κ(p) ⊗[R] (R ⊗[A] B)` for every prime `p`
of `R`, then `1 ⊗ b` is a nonzerodivisor on `R ⊗[A] B`. Neither `R` nor `R ⊗[A] B` need be
noetherian. -/
theorem isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber [IsNoetherianRing A]
    [IsNoetherianRing B] [Flat A B] {b : B}
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsSMulRegular (p.Fiber (R ⊗[A] B)) ((1 : p.ResidueField) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] b))) :
    IsSMulRegular (R ⊗[A] B) ((1 : R) ⊗ₜ[A] b) := by
  refine .of_right_eq_zero_of_smul fun x hx ↦ ?_
  by_contra hx0
  -- A maximal ideal `q` containing the annihilator of `x`.
  obtain ⟨q, hq, hxq⟩ := Ideal.exists_le_maximal (Submodule.span (R ⊗[A] B) {x}).annihilator
    (by rwa [Ne, Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot])
  -- The primes of `B` and `R` under `q` lie over the same prime of `A`.
  let r := q.comap (includeRight : B →ₐ[A] R ⊗[A] B)
  let p := q.comap (algebraMap R (R ⊗[A] B))
  have hr : r.comap (algebraMap A B) = p.comap (algebraMap A R) := by
    ext a
    simp only [r, p, Ideal.mem_comap, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  obtain ⟨hreg, _⟩ := isSMulRegular_localization_of_isSMulRegular_fiber _
    (isSMulRegular_fiber_comap (A := A) (B := B) p (h p)) r hr
  let Br := Localization.AtPrime r
  -- `1 ⊗ b` is a nonzerodivisor on `R ⊗[A] B_r`, the localization of `R ⊗[A] B` at the image of
  -- `B ∖ r`, so `x` is killed there.
  have hreg' := isSMulRegular_one_tmul_of_quotient_span_singleton (R := A) hreg R
  let g : R ⊗[A] B →ₐ[R] R ⊗[A] Br := map (AlgHom.id R R) (IsScalarTower.toAlgHom A B Br)
  let := g.toRingHom.toAlgebra
  have : IsScalarTower R (R ⊗[A] B) (R ⊗[A] Br) :=
    .of_algebraMap_eq fun x ↦ by simp [RingHom.algebraMap_toAlgebra, g]
  have := IsLocalization.tensorProduct_tensorProduct_right A R r.primeCompl Br
    (by ext; simp [RingHom.algebraMap_toAlgebra, g])
  have hgx : algebraMap (R ⊗[A] B) (R ⊗[A] Br) x = 0 := by
    refine hreg'.right_eq_zero_of_smul ?_
    have := congrArg (algebraMap (R ⊗[A] B) (R ⊗[A] Br)) hx
    rw [smul_eq_mul, map_mul, map_zero] at this
    simpa [RingHom.algebraMap_toAlgebra, g] using this
  -- Hence `x` is killed by some `1 ⊗ s` with `s ∉ r`, that is, `1 ⊗ s ∉ q`.
  obtain ⟨⟨_, s, hs, rfl⟩, hsx⟩ := (IsLocalization.map_eq_zero_iff
    (r.primeCompl.map (includeRight (R := A) (A := R))) (R ⊗[A] Br) x).mp hgx
  exact hs (hxq ((Submodule.mem_annihilator_span_singleton _ _).mpr hsx))

end Module.Flat

namespace Ideal

/-- Fibrewise regularity is preserved by extension of the residue field under base change. -/
theorem isSMulRegular_fiber_baseChange {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B] (p : Ideal R) [p.IsPrime] {b : B}
    (h : IsSMulRegular ((p.comap (algebraMap A R)).Fiber B)
      ((1 : (p.comap (algebraMap A R)).ResidueField) ⊗ₜ[A] b)) :
    IsSMulRegular (p.Fiber (R ⊗[A] B))
      ((1 : p.ResidueField) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] b)) := by
  let p₀ := p.comap (algebraMap A R)
  let ι : p₀.ResidueField →ₐ[A] p.ResidueField :=
    Ideal.ResidueField.mapₐ p₀ p (Algebra.ofId A R) rfl
  let := ι.toRingHom.toAlgebra
  have : IsScalarTower A p₀.ResidueField p.ResidueField :=
    .of_algebraMap_eq fun a ↦ (ι.commutes a).symm
  let e := cancelBaseChange A p₀.ResidueField p.ResidueField p.ResidueField B
  have h' := Module.Flat.isSMulRegular_one_tmul_of_quotient_span_singleton
    (R := p₀.ResidueField) h p.ResidueField
  have he := (TauCeti.isSMulRegular_map_iff e _).mpr h'
  let e' := cancelBaseChange A R p.ResidueField p.ResidueField B
  apply (TauCeti.isSMulRegular_map_iff e' _).mp
  simpa only [e', e, cancelBaseChange_tmul, one_smul] using he

end Ideal

/-! ### Universal regularity near a flat fibre point -/



namespace Algebra

open Module

private theorem exists_notMem_flat_localizedModule_quotient
    {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [IsNoetherianRing R]
    [Algebra.FiniteType R B] (prime : Ideal B) [prime.IsPrime]
    [Flat R (Localization.AtPrime prime)] (b : B)
    (hfib : ∀ x : Localization.AtPrime prime,
      algebraMap B _ b * x ∈
        (prime.comap (algebraMap R B)).map (algebraMap R _) →
      x ∈ (prime.comap (algebraMap R B)).map
        (algebraMap R (Localization.AtPrime prime))) :
    ∃ g ∉ prime,
      (∀ x : B, b * x = 0 → g * x = 0) ∧
      Flat R (LocalizedModule (Submonoid.powers g)
        (B ⧸ Ideal.span {b})) := by
  classical
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  let C := B ⧸ Ideal.span {b}
  let Sq := Localization.AtPrime prime
  obtain ⟨hreg', hflat⟩ := Module.Flat.isSMulRegular_and_flat_quotient_localization prime b
    ((isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr hfib)
  have hreg (x : Sq) (hx : algebraMap B Sq b * x = 0) : x = 0 :=
    hreg'.right_eq_zero_of_smul hx
  have hflatq : Flat R (LocalizedModule prime.primeCompl C) :=
    (flat_localizedModule_quotient_span_singleton_iff b prime.primeCompl Sq).mpr hflat
  obtain ⟨g₁, hg₁, hopen⟩ := Module.Flat.exists_notMem_forall_flat_localizedModule
    (M := C) prime hflatq
  set L := LinearMap.ker (LinearMap.mulLeft B b)
  obtain ⟨g₂, hg₂, hg₂K⟩ := exists_notMem_forall_smul_eq_zero (P := prime) L
    fun x ↦ by
      have hxK : b * x = 0 := LinearMap.mem_ker.mp x.property
      have : algebraMap B Sq x = 0 := hreg _ (by rw [← map_mul, hxK, map_zero])
      obtain ⟨⟨t, ht⟩, htx⟩ :=
        (IsLocalization.map_eq_zero_iff prime.primeCompl Sq (x : B)).mp this
      exact ⟨t, ht, Subtype.ext htx⟩
  refine ⟨g₁ * g₂, fun h ↦ (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹_›).mp h |>.elim
    hg₁ hg₂,
    fun x hx ↦ ?_, ?_⟩
  · have hzero := congrArg Subtype.val (hg₂K ⟨x, LinearMap.mem_ker.mpr hx⟩)
    -- The kernel subtype has the ring's self-module action, hence multiplication.
    change g₂ * x = 0 at hzero
    rw [mul_assoc, hzero, mul_zero]
  · rw [Module.Flat.iff_lTensor_injective']
    intro I
    rw [IsLocalizedModule.lTensor_injective_iff (Submonoid.powers (g₁ * g₂))
      (LocalizedModule.mkLinearMap (Submonoid.powers (g₁ * g₂)) C)]
    intro y hy
    obtain ⟨n, hn⟩ := Module.pow_smul_eq_zero_of_flat_localizedModule
      (R := R) (S := B) (M := C) (a := g₁)
      (fun q hq ↦ hopen q.asIdeal hq) I.subtype Subtype.val_injective y hy
    exact ⟨(g₁ * g₂) ^ n, ⟨n, rfl⟩, by rw [mul_pow, mul_comm, mul_smul, hn, smul_zero]⟩

end Algebra

namespace Algebra

open Module

/-- An equation regular on the fibre at a flat point becomes universally regular on a principal
neighbourhood: its kernel after any tensor product is annihilated by powers of one denominator. -/
theorem _root_.Ideal.exists_notMem_forall_pow_smul_eq_zero
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [IsNoetherianRing R]
    [Algebra.FiniteType R B] (q : Ideal B) [q.IsPrime]
    [Flat R (Localization.AtPrime q)] (b : B)
    (h : ∀ x : Localization.AtPrime q,
      algebraMap B _ b * x ∈ (q.comap (algebraMap R B)).map (algebraMap R _) →
      x ∈ (q.comap (algebraMap R B)).map (algebraMap R (Localization.AtPrime q))) :
    ∃ g ∉ q, ∀ (N : Type*) [AddCommGroup N] [Module R N] (x : B ⊗[R] N),
      b • x = 0 → ∃ n : ℕ, g ^ n • x = 0 := by
  obtain ⟨g, hg, hreg, hflat⟩ := exists_notMem_flat_localizedModule_quotient q b h
  refine ⟨g, hg, fun N _ _ x hx ↦ ?_⟩
  let Bg := Localization.Away g
  have hreg' : IsSMulRegular Bg (algebraMap B Bg b) :=
    IsLocalization.Away.isSMulRegular_algebraMap hreg
  have : Flat R (Bg ⧸ Ideal.span {algebraMap B Bg b}) :=
    (flat_localizedModule_quotient_span_singleton_iff b (Submonoid.powers g) Bg).mp hflat
  let ℓ : B ⊗[R] N →ₗ[B] Bg ⊗[R] N :=
    AlgebraTensorModule.rTensor R N (Algebra.linearMap B Bg)
  have : IsLocalizedModule (Submonoid.powers g) ℓ :=
    IsLocalizedModule.rTensor (A := B) _ _
  have hinj : Function.Injective ((LinearMap.mulLeft R (algebraMap B Bg b)).rTensor N) :=
    ((LinearMap.mulLeft R (algebraMap B Bg b)).lTensor_inj_iff_rTensor_inj N).mp
      (Module.Flat.lTensor_mulLeft_injective_of_quotient_span_singleton hreg' N)
  have hzero : ℓ x = 0 := (injective_iff_map_eq_zero _).mp hinj _ <| by
    -- The tensor of multiplication is the localized algebra's scalar action.
    change algebraMap B Bg b • ℓ x = 0
    rw [algebraMap_smul, ← map_smul, hx, map_zero]
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) (f := ℓ)).mp
    hzero
  exact ⟨n, hn⟩

end Algebra
