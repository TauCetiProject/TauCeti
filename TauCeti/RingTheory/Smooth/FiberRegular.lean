/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Smooth.Flat
import TauCeti.Algebra.Regular.SMul
import TauCeti.RingTheory.Flat.QuotSMulTop
import TauCeti.RingTheory.Flat.QuotientRegular
import TauCeti.RingTheory.LocalRing.ResidueField.Fiber
import TauCeti.RingTheory.Smooth.NoetherianDescent

/-!
# Nonzerodivisors on the fibres of a smooth algebra

Let `B` be a smooth algebra over a commutative ring `R`, and let `b ∈ B`. If `1 ⊗ b` is a
nonzerodivisor on the fibre ring `κ(p) ⊗[R] B` for every prime `p` of `R`, then `b` is a
nonzerodivisor on `B` (`Algebra.Smooth.isSMulRegular_of_forall_isSMulRegular_fiber`). No
noetherian hypothesis is made on `R` or `B`.

Geometrically, for a smooth morphism `X ⟶ S`, a function on `X` which is a nonzerodivisor on every
fibre is a nonzerodivisor on `X`. This is the local algebra behind the fibre criterion for relative
effective Cartier divisors over an arbitrary base.

Over a noetherian base this is the local flatness argument of
`Module.Flat.isSMulRegular_of_isSMulRegular_quotient`. The general case is reduced to it by a
noetherian model, which is where smoothness is used: `B` is the base change `R ⊗[A] B₀` of a
smooth algebra `B₀` over a noetherian ring `A`, in such a way that `b` is the image of some
`b₀ ∈ B₀` (`Algebra.Smooth.exists_isNoetherianRing_and_eq_one_tmul`). Then `B₀` is noetherian and
flat over `A`, and the following steps apply to any such model
(`Module.Flat.isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber`).

1. Let `q` be a prime of `R ⊗[A] B₀`, lying over the prime `p` of `R`, the prime `r` of `B₀` and
   the prime `p₀` of `A`. The fibre ring `κ(p₀) ⊗[A] B₀` embeds into `κ(p) ⊗[R] (R ⊗[A] B₀)`,
   since `B₀` is flat over `A`. So `b₀` is a nonzerodivisor on it.
2. By the local criterion over the noetherian local ring `A_{p₀}`, `b₀` is a nonzerodivisor on
   `(B₀)_r` and `(B₀)_r ⧸ (b₀)` is flat over `A`.
3. Hence `1 ⊗ b₀` stays a nonzerodivisor on `R ⊗[A] (B₀)_r`, the localization of `R ⊗[A] B₀` at the
   image of `B₀ ∖ r`. An element killed by `1 ⊗ b₀` is therefore killed by some `1 ⊗ s` with
   `s ∉ r`, which lies outside `q`. Its annihilator lies in no prime, so the element is zero.

## Main results

* `Module.Flat.isSMulRegular_localization_of_isSMulRegular_fiber`: for a noetherian flat algebra
  `B` over a noetherian ring `A`, an element which is a nonzerodivisor on the fibre ring over a
  prime `p` of `A` is a nonzerodivisor on `B_r` for every prime `r` over `p`, with `B_r ⧸ (b)`
  flat over `A`.
* `Module.Flat.isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber`: for a noetherian flat
  algebra `B` over a noetherian ring `A` and any `A`-algebra `R`, an element `b ∈ B` whose image is
  a nonzerodivisor on every fibre of `R ⊗[A] B` over `R` has `1 ⊗ b` a nonzerodivisor on
  `R ⊗[A] B`.
* `Algebra.Smooth.isSMulRegular_of_forall_isSMulRegular_fiber`: the statement for smooth
  algebras.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 22.5 and its Corollary, for the noetherian
  case.
* The Stacks Project, *Divisors*, section *Relative effective Cartier divisors*, for the fibre
  criterion this serves.
-/

public section

open TensorProduct Algebra.TensorProduct
open scoped Pointwise

universe u

variable {A R B : Type*} [CommRing A] [CommRing R] [CommRing B] [Algebra A R] [Algebra A B]

namespace Module.Flat

/-- Let `B` be flat over `A`, let `R` be an `A`-algebra and `p` a prime of `R`, lying over the prime
`p₀` of `A`. If `1 ⊗ (1 ⊗ b)` is a nonzerodivisor on the fibre ring `κ(p) ⊗[R] (R ⊗[A] B)`, then
`1 ⊗ b` is a nonzerodivisor on `κ(p₀) ⊗[A] B`, which embeds into it. -/
private theorem isSMulRegular_fiber_comap [Flat A B] (p : Ideal R) [p.IsPrime] {b : B}
    (h : IsSMulRegular (p.Fiber (R ⊗[A] B)) ((1 : p.ResidueField) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] b))) :
    IsSMulRegular ((p.comap (algebraMap A R)).Fiber B)
      ((1 : (p.comap (algebraMap A R)).ResidueField) ⊗ₜ[A] b) := by
  let p₀ := p.comap (algebraMap A R)
  let ι : p₀.ResidueField →ₐ[A] p.ResidueField :=
    Ideal.ResidueField.mapₐ p₀ p (Algebra.ofId A R) rfl
  -- `κ(p₀) ⊗[A] B → κ(p) ⊗[A] B ≃ κ(p) ⊗[R] (R ⊗[A] B)`, injective as `B` is flat.
  let φ : p₀.Fiber B →ₐ[A] p.Fiber (R ⊗[A] B) :=
    ((cancelBaseChange A R p.ResidueField p.ResidueField B).symm.toAlgHom.restrictScalars A).comp
      (map ι (AlgHom.id A B))
  have hφ : Function.Injective φ :=
    (cancelBaseChange A R p.ResidueField p.ResidueField B).symm.injective.comp
      (rTensor_preserves_injective_linearMap (M := B) ι.toLinearMap ι.injective)
  have hb : φ ((1 : p₀.ResidueField) ⊗ₜ[A] b) = (1 : p.ResidueField) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] b) := by
    simp [φ]
  intro x y hxy
  refine hφ (h ?_)
  simp only [smul_eq_mul] at hxy ⊢
  rw [← hb, ← map_mul, ← map_mul, hxy]

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
  let Ap := Localization.AtPrime p
  let Br := Localization.AtPrime r
  let := Localization.AtPrime.algebraOfLiesOver p r
  have : IsLocalHom (algebraMap Ap Br) := Localization.isLocalHom_localRingHom _ _ _ _
  have : Flat Ap Br := by
    rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) _ _ _
  -- `b` is a nonzerodivisor on the closed fibre `B_r ⧸ p B_r ≃ (κ(p) ⊗[A] B)_Q`.
  have hloc : IsSMulRegular (Localization.AtPrime Q)
      (algebraMap (p.Fiber B) _ ((1 : p.ResidueField) ⊗ₜ[A] b)) := hb.of_flat
  let e := (Ideal.Fiber.localizationAlgEquivQuotient p Q).toRingEquiv
  have he : e (algebraMap (p.Fiber B) _ ((1 : p.ResidueField) ⊗ₜ[A] b)) =
      Ideal.Quotient.mk _ (algebraMap B Br b) := by
    simp [e, Br, r, Ideal.Fiber.localizationAlgEquivQuotient, ← Ideal.Quotient.mk_algebraMap]
  have hmax : ((IsLocalRing.maximalIdeal Ap).map (algebraMap Ap Br) • ⊤ : Submodule Br Br) =
      p.map (algebraMap A Br) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, smul_eq_mul, Ideal.mul_top]
  have hfib : IsSMulRegular (Br ⧸ ((IsLocalRing.maximalIdeal Ap).map (algebraMap Ap Br) • ⊤ :
      Submodule Br Br)) (algebraMap B Br b) := by
    rw [hmax, ← isSMulRegular_algebraMap_iff (A := Br ⧸ p.map (algebraMap A Br)),
      Ideal.Quotient.algebraMap_eq, ← he]
    exact (TauCeti.isSMulRegular_map_iff e _).mpr hloc
  -- The local criterion over the noetherian local ring `A_p`.
  refine ⟨isSMulRegular_of_isSMulRegular_quotient hfib, ?_⟩
  have := quotSMulTop_of_isSMulRegular_quotient hfib
  have : Flat A (QuotSMulTop (algebraMap B Br b) Br) := .trans A Ap _
  exact .of_linearEquiv ((Submodule.quotEquivOfEq (Ideal.span {algebraMap B Br b})
    (algebraMap B Br b • ⊤ : Submodule Br Br) (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])).restrictScalars A)

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

namespace Algebra.Smooth

/-- **Nonzerodivisors on the fibres of a smooth algebra.** Let `B` be a smooth `R`-algebra and
`b ∈ B`. If `1 ⊗ b` is a nonzerodivisor on the fibre ring `κ(p) ⊗[R] B` for every prime `p` of
`R`, then `b` is a nonzerodivisor on `B`. -/
theorem isSMulRegular_of_forall_isSMulRegular_fiber {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] [Smooth R B] {b : B}
    (h : ∀ (p : Ideal R) [p.IsPrime], IsSMulRegular (p.Fiber B) ((1 : p.ResidueField) ⊗ₜ[R] b)) :
    IsSMulRegular B b := by
  -- A noetherian model `R ⊗[A] B₀` of `B` in which `b` is `1 ⊗ b₀`.
  obtain ⟨A, B₀, _, _, _, _, _, _, e, b₀, heb⟩ := exists_isNoetherianRing_and_eq_one_tmul (A := R) b
  have : IsNoetherianRing B₀ := FiniteType.isNoetherianRing A B₀
  rw [← TauCeti.isSMulRegular_map_iff e, heb]
  refine Module.Flat.isSMulRegular_one_tmul_of_forall_isSMulRegular_fiber fun p _ ↦ ?_
  have := (TauCeti.isSMulRegular_map_iff
    (congr (AlgEquiv.refl : p.ResidueField ≃ₐ[R] _) e) _).mpr (h p)
  simpa [heb] using this

end Algebra.Smooth
