/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Localization at the maximal ideal of a local ring and at its preimages, and local lifts

Every element of a local ring `S` outside its maximal ideal is a unit, so the localization of `S`
at its maximal ideal inverts only units and is `S` itself (Mathlib `IsLocalization.atUnits`).
This file names that equivalence, as an isomorphism of `R`-algebras for any `R`-algebra
structure on `S`, so that statements about `Localization.AtPrime (maximalIdeal S)` transfer to
`S` along a single map.

More generally, if a prime ideal `q` of an `R`-algebra `S` lies over the maximal ideal of a local
ring `R`, then the algebra map from `R` to any localization of `S` at `q` is local. Likewise, a ring
homomorphism `f : A →+* R` to a local ring extends to a local homomorphism from any localization of
`A` at the preimage `f⁻¹(𝔪_R)`. Hence an element whose image under `f` lies outside `𝔪_Rⁿ` stays
outside the `n`-th power of the maximal ideal of that localization.
For `f` the constant coefficient map of a polynomial ring over `R`, this says that a polynomial
whose constant coefficient lies outside `𝔪_R²` does not lie in the square of the maximal ideal of
the polynomial ring localized at `(𝔪_R, X_i)`.

Similarly, let `ε : A →ₐ[k] k` be a `k`-point of a `k`-algebra `A` over a field `k`, and let
`ψ : A →ₐ[k] B` be a map to a local `k`-algebra sending the kernel of `ε` into the maximal ideal
(it suffices to check this on generators of `A` at which `ε` vanishes). Then `ψ` extends to the
local ring of `A` at `ε`. More generally, a divisibility `u ∈ (v)` in a localization of `A` at
a submonoid `M` forces `ψ u ∈ (ψ v)` for every ring map `ψ` sending `M` to units.

A homomorphism `ψ : R →+* T` to a local ring which inverts the complement of a prime
`p` and maps `p` into the maximal ideal lifts to a local homomorphism from the localization of `R`
at `p`. For instance, a homomorphism to a field factors locally through the localization at its
kernel.

## Main results

* `IsLocalRing.algEquivLocalizationAtMaximalIdeal R S`: the `R`-algebra isomorphism from a local
  ring `S` to its localization at its maximal ideal.
* `IsLocalization.AtPrime.isLocalHom_lift`: the lift of a homomorphism to a local ring along the
  localization at a prime mapped into the maximal ideal is local.
* `IsLocalization.AtPrime.isLocalHom_algebraMap_of_liesOver` and
  `Localization.AtPrime.isLocalHom_algebraMap_of_liesOver`: if `q` lies over `maximalIdeal R`, the
  algebra map from `R` to a localization at `q` is local.
* `TauCeti.algebraMap_notMem_maximalIdeal_pow`: an element whose image under `f : A →+* R` is not
  in `𝔪_Rⁿ` does not lie in the `n`-th power of the maximal ideal of a localization of `A` at
  `f⁻¹(𝔪_R)`.
* `TauCeti.ker_le_comap_maximalIdeal_of_adjoin_eq_top`: a `k`-algebra map to a local ring sending
  generators that vanish at a `k`-point `ε` into the maximal ideal sends the kernel of `ε` there.
* `TauCeti.isUnit_apply_of_notMem_ker`: such a map sends every element outside the kernel of `ε`
  to a unit.
* `TauCeti.algebraMap_notMem_span_singleton`: if `ψ` inverts `M` and `ψ u ∉ (ψ v)`, then
  `u ∉ (v)` in a localization of `A` at `M`.
-/

public section

namespace IsLocalRing

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S] [IsLocalRing S]

/-- A local `R`-algebra `S` is isomorphic, as an `R`-algebra, to its localization at its maximal
ideal: that localization inverts only units. -/
noncomputable def algEquivLocalizationAtMaximalIdeal :
    S ≃ₐ[R] Localization.AtPrime (maximalIdeal S) :=
  (IsLocalization.atUnits S (maximalIdeal S).primeCompl
    fun _ hx ↦ notMem_maximalIdeal.mp hx).restrictScalars R

/-- The local-ring equivalence maps an element to its image in the localization. -/
@[simp]
theorem algEquivLocalizationAtMaximalIdeal_apply (s : S) :
    algEquivLocalizationAtMaximalIdeal R S s =
      algebraMap S (Localization.AtPrime (maximalIdeal S)) s := by
  simpa only [algEquivLocalizationAtMaximalIdeal, AlgEquiv.restrictScalars_apply,
    Algebra.algebraMap_self_apply] using
    (IsLocalization.atUnits S (maximalIdeal S).primeCompl
      fun _ hx ↦ notMem_maximalIdeal.mp hx).commutes s

end IsLocalRing

namespace IsLocalization.AtPrime

open IsLocalRing

variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T] [Algebra R S]
  [IsLocalRing T] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]

/-- Let `ψ : R →+* T` be a homomorphism to a local ring which inverts the complement of a prime `p`
and maps `p` into the maximal ideal. Its lift to the localization `S` of `R` at `p` is a local
homomorphism. For `T` a field, `p` can be the kernel of `ψ`. -/
theorem isLocalHom_lift {ψ : R →+* T} (hψ : ∀ y : p.primeCompl, IsUnit (ψ y))
    (hp : p ≤ (maximalIdeal T).comap ψ) : IsLocalHom (IsLocalization.lift hψ : S →+* T) := by
  have := isLocalRing S p
  -- The maximal ideal of `S` is generated by `p`, which the lift sends to `ψ(p) ⊆ 𝔪_T`.
  refine ((local_hom_tfae _).out 1 3).mpr ?_
  rw [← map_eq_maximalIdeal p S, Ideal.map_map, IsLocalization.lift_comp]
  exact Ideal.map_le_iff_le_comap.mpr hp

/-- If `q` is a prime ideal of an `R`-algebra `S` lying over the maximal ideal of the local ring
`R`, then the algebra map from `R` to any localization `T` of `S` at `q` is local. -/
theorem isLocalHom_algebraMap_of_liesOver {R S T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalRing R] (q : Ideal S) [q.IsPrime] [IsLocalization.AtPrime T q]
    [q.LiesOver (maximalIdeal R)] :
    IsLocalHom (algebraMap R T) := by
  have := isLocalRing T q
  -- `𝔪_T` lies over `q`, which lies over `𝔪_R`.
  refine ((local_hom_tfae _).out 1 5).mpr ?_
  rw [← Ideal.under_def, ← Ideal.under_under (B := S), under_maximalIdeal T q,
    ← q.over_def (maximalIdeal R)]

end IsLocalization.AtPrime

namespace Localization.AtPrime

/-- If `q` is a prime ideal of an `R`-algebra `S` lying over the maximal ideal of the local ring
`R`, then `algebraMap R (Localization.AtPrime q)` is a local homomorphism. -/
theorem isLocalHom_algebraMap_of_liesOver {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [IsLocalRing R] (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    IsLocalHom (algebraMap R (Localization.AtPrime q)) :=
  IsLocalization.AtPrime.isLocalHom_algebraMap_of_liesOver q

end Localization.AtPrime

namespace TauCeti

open _root_.IsLocalRing Ideal

variable {A R : Type*} [CommSemiring A] [CommSemiring R] [IsLocalRing R]

/-- Let `f : A →+* R` be a ring homomorphism to a local ring. An element of `A` whose image under
`f` is not in `𝔪_Rⁿ` does not lie in the `n`-th power of the maximal ideal of a localization `L` of
`A` at `f⁻¹(𝔪_R)`: `f` extends to a local homomorphism `L →+* R`. -/
theorem algebraMap_notMem_maximalIdeal_pow {L : Type*} [CommSemiring L] [Algebra A L]
    {f : A →+* R} [IsLocalization.AtPrime L ((maximalIdeal R).comap f)] [IsLocalRing L]
    {n : ℕ} {a : A} (ha : f a ∉ maximalIdeal R ^ n) :
    algebraMap A L a ∉ maximalIdeal L ^ n := by
  have hf (s : ((maximalIdeal R).comap f).primeCompl) : IsUnit (f s) :=
    notMem_maximalIdeal.mp s.property
  -- The extension `L →+* R` of `f` is local, so it maps `𝔪_Lⁿ` into `𝔪_Rⁿ`.
  have := IsLocalization.AtPrime.isLocalHom_lift (S := L) _ hf le_rfl
  refine fun h ↦ ha ?_
  rw [← IsLocalization.lift_eq (S := L) hf a]
  exact le_comap_pow _ n (maximalIdeal_comap (IsLocalization.lift (S := L) hf) ▸ h)

/-- Let `L` be a localization of `A` at a submonoid `M`, and let `ψ` be a ring homomorphism from `A`
sending `M` to units. If `ψ u ∉ (ψ v)`, then `u ∉ (v)` in `L`. -/
theorem algebraMap_notMem_span_singleton {B L F : Type*} [CommSemiring B] [CommSemiring L]
    [Algebra A L] {M : Submonoid A} [IsLocalization M L] [FunLike F A B] [RingHomClass F A B]
    {ψ : F} (hψ : ∀ m : M, IsUnit (ψ m)) {u v : A} (h : ψ u ∉ span {ψ v}) :
    algebraMap A L u ∉ span {algebraMap A L v} := by
  have hM (m : M) : IsUnit ((ψ : A →+* B) m) := hψ m
  have hL (a : A) : IsLocalization.lift (S := L) hM (algebraMap A L a) = ψ a :=
    IsLocalization.lift_eq hM a
  intro hmem
  obtain ⟨c, hc⟩ := mem_span_singleton'.mp hmem
  refine h (mem_span_singleton'.mpr ⟨IsLocalization.lift (S := L) hM c, ?_⟩)
  rw [← hL, ← hL, ← hc, map_mul]

section Point

variable {k A B : Type*} [CommRing A] [CommRing B] [IsLocalRing B]

/-- Let `ε : A →ₐ[k] k` be a `k`-point of a `k`-algebra `A` generated by `s`, and let
`ψ : A →ₐ[k] B` be a map to a local `k`-algebra. If the elements of `s` vanish at `ε` and `ψ` sends
them into the maximal ideal of `B`, then `ψ` sends the kernel of `ε` into the maximal ideal. -/
theorem ker_le_comap_maximalIdeal_of_adjoin_eq_top [CommRing k] [Algebra k A] [Algebra k B]
    {s : Set A} (hs : Algebra.adjoin k s = ⊤) (ε : A →ₐ[k] k) (hε : ∀ a ∈ s, ε a = 0)
    (ψ : A →ₐ[k] B) (hψ : ∀ a ∈ s, ψ a ∈ maximalIdeal B) :
    RingHom.ker ε.toRingHom ≤ (maximalIdeal B).comap ψ := by
  -- `ψ a` and `ε a` agree modulo the maximal ideal of `B`, for every `a`.
  have hm (a : A) : ψ a - algebraMap k B (ε a) ∈ maximalIdeal B := by
    have ha : a ∈ Algebra.adjoin k s := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha => simpa [hε a ha] using hψ a ha
    | algebraMap c => simp
    | add a b _ _ ha hb => simpa [add_sub_add_comm] using add_mem ha hb
    | mul a b _ _ ha hb =>
      convert add_mem (Ideal.mul_mem_right (ψ b) _ ha)
        (Ideal.mul_mem_left _ (algebraMap k B (ε a)) hb) using 1
      simp only [map_mul]
      ring
  intro a ha
  have ha : ε a = 0 := RingHom.mem_ker.mp ha
  simpa [ha] using hm a

variable [Field k] [Algebra k A] [Algebra k B]

/-- A `k`-algebra map `ψ` to a local ring which sends the kernel of a `k`-point `ε` into the
maximal ideal sends every element outside that kernel to a unit. -/
theorem isUnit_apply_of_notMem_ker {ε : A →ₐ[k] k} {ψ : A →ₐ[k] B}
    (hψ : RingHom.ker ε.toRingHom ≤ (maximalIdeal B).comap ψ) {a : A}
    (ha : a ∉ RingHom.ker ε.toRingHom) : IsUnit (ψ a) := by
  -- `ψ a` differs from the unit `ε a` by an element of the maximal ideal.
  have hm : ψ a - algebraMap k B (ε a) ∈ maximalIdeal B := by
    simpa using hψ (show a - algebraMap k A (ε a) ∈ RingHom.ker ε.toRingHom by simp)
  have hu : IsUnit (algebraMap k B (ε a)) :=
    (isUnit_iff_ne_zero.mpr fun h ↦ ha (by simpa using h)).map _
  by_contra hn
  exact (mem_maximalIdeal _).mp (by simpa using sub_mem ((mem_maximalIdeal _).mpr hn) hm) hu

end Point

end TauCeti
