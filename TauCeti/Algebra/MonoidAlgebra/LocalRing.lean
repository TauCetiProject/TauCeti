/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.FiniteType
public import TauCeti.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp
import TauCeti.Algebra.MonoidAlgebra.Exactness

/-!
# Monoid algebras over a local ring

For a finite monoid `G` (for instance a finite group) and a local ring `R` with residue field `k`,
the free module `R[G]^ι` of finite rank is a finitely generated `R`-module, so Nakayama's lemma
over `R` detects surjectivity of its endomorphisms after reduction to `k[G]^ι`.
The Orzech property then upgrades surjectivity to bijectivity.

For a finite commutative `p`-group `Q` and a local ring `R` in which `p` is not a unit, the group
algebra `R[Q]` is itself local, and the augmentation `R[Q] → R` is a local homomorphism: an element
of `R[Q]` is a unit as soon as its augmentation is. Indeed every maximal ideal of `R[Q]` lies over
the maximal ideal of `R`, because `R[Q]` is finite over `R`, so its residue field has
characteristic `p`; there `q - 1` is nilpotent, as `(q - 1) ^ (p ^ k) = q ^ (p ^ k) - 1 = 0`, and
therefore zero. So every maximal ideal contains the augmentation ideal.

## Main results

* `TauCeti.MonoidAlgebra.bijective_of_forall_exists_mapRingHom_residue_eq`: an `R[G]`-linear
  endomorphism of `R[G]^ι` that is onto modulo the maximal ideal is bijective.
* `TauCeti.MonoidAlgebra.isLocalHom_lift_one_of_isPGroup`: for a finite commutative `p`-group `Q`
  the augmentation `R[Q] → R` is a local homomorphism.
* `TauCeti.MonoidAlgebra.isLocalRing_of_isPGroup`: `R[Q]` is a local ring.
-/

public section

open MonoidAlgebra IsLocalRing

namespace TauCeti.MonoidAlgebra

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Monoid G] [Finite G] {ι : Type*}
  [Finite ι]

/-- **Nakayama's lemma for `R[G]^ι`.** An `R[G]`-linear endomorphism of `R[G]^ι` that is onto
modulo the maximal ideal is bijective. -/
theorem bijective_of_forall_exists_mapRingHom_residue_eq
    (θ : (ι → MonoidAlgebra R G) →ₗ[MonoidAlgebra R G] (ι → MonoidAlgebra R G))
    (h : ∀ y : ι → MonoidAlgebra R G, ∃ x, ∀ i,
      mapRingHom G (residue R) (θ x i) = mapRingHom G (residue R) (y i)) :
    Function.Bijective θ := by
  classical
  have := Fintype.ofFinite ι
  -- `R[G]^ι` is a finitely generated `R`-module and `θ` is onto modulo `𝔪 • R[G]^ι`.
  have hle : (⊤ : Submodule R (ι → MonoidAlgebra R G)) ≤
      LinearMap.range (θ.restrictScalars R) ⊔ maximalIdeal R • ⊤ := by
    intro y _
    obtain ⟨x, hx⟩ := h y
    refine Submodule.mem_sup.mpr ⟨θ x, ⟨x, rfl⟩, y - θ x, ?_, add_sub_cancel _ _⟩
    rw [← Finset.univ_sum_single (y - θ x)]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_top_le_comap_smul_top _
      (LinearMap.single R (fun _ ↦ MonoidAlgebra R G) i) ?_
    rw [← ker_residue, ← mapRingHom_eq_zero_iff, Pi.sub_apply, map_sub, hx, sub_self]
  have hsurj : Function.Surjective θ := LinearMap.range_eq_top.mp (top_unique
    (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson ⊥)
      hle))
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism (θ.restrictScalars R) hsurj, hsurj⟩

section PGroup

variable {R : Type*} [CommRing R] [IsLocalRing R] {p : ℕ} [Fact p.Prime] {Q : Type*} [CommGroup Q]
  [Finite Q]

/-- Every maximal ideal of `R[Q]` contains `q - 1` for each `q` in the `p`-group `Q`. -/
private theorem single_sub_one_mem_of_isMaximal (hp : ¬IsUnit (p : R)) (hQ : IsPGroup p Q)
    (𝔐 : Ideal (MonoidAlgebra R Q)) [𝔐.IsMaximal] (q : Q) : single q (1 : R) - 1 ∈ 𝔐 := by
  -- `𝔐` lies over the maximal ideal of `R`, which contains `p`.
  have hcomap : 𝔐.comap (algebraMap R (MonoidAlgebra R Q)) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔐)
  have hp𝔐 : (p : MonoidAlgebra R Q) ∈ 𝔐 := by
    rw [← map_natCast (algebraMap R (MonoidAlgebra R Q)), ← Ideal.mem_comap, hcomap]
    exact hp
  -- In the residue field of `𝔐`, of characteristic `p`, the element `q - 1` is nilpotent.
  let _ := Ideal.Quotient.field 𝔐
  have : CharP (MonoidAlgebra R Q ⧸ 𝔐) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk 𝔐), Ideal.Quotient.eq_zero_iff_mem]
    exact hp𝔐
  obtain ⟨k, hk⟩ := hQ q
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero)]
  simp [sub_pow_char_pow, ← map_pow, single_pow, hk, ← one_def]

/-- **The augmentation of the group algebra of a `p`-group is local.** For a finite commutative
`p`-group `Q` and a local ring `R` in which `p` is not a unit, the augmentation `R[Q] → R` is a
local homomorphism: an element of `R[Q]` whose augmentation is a unit is a unit. -/
theorem isLocalHom_lift_one_of_isPGroup (hp : ¬IsUnit (p : R)) (hQ : IsPGroup p Q) :
    IsLocalHom (MonoidAlgebra.lift R R Q 1) := by
  refine ⟨fun x hx ↦ ?_⟩
  by_contra hx'
  obtain ⟨𝔐, h𝔐, hx𝔐⟩ := Ideal.exists_le_maximal (Ideal.span {x})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hx𝔐 : x ∈ 𝔐 := hx𝔐 (Ideal.subset_span rfl)
  -- `𝔐` contains the augmentation ideal, which is generated by the differences `q - 1`.
  have hker : RingHom.ker (augmentation R Q) ≤ 𝔐 := by
    rw [ker_augmentation_eq_span, Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    exact single_sub_one_mem_of_isMaximal hp hQ 𝔐 q
  have haug : (MonoidAlgebra.lift R R Q 1 : MonoidAlgebra R Q →+* R) = augmentation R Q :=
    MonoidAlgebra.ringHom_ext (fun _ ↦ by simp [MonoidAlgebra.lift_single]) fun _ ↦ by
      simp [MonoidAlgebra.lift_single]
  -- `x` differs from the constant `algebraMap (augmentation x)` by an element of `𝔐`.
  have hdiff : ∀ y : MonoidAlgebra R Q,
      algebraMap R (MonoidAlgebra R Q) (MonoidAlgebra.lift R R Q 1 y) - y ∈ 𝔐 := fun y ↦
    hker <| by
      rw [RingHom.mem_ker, map_sub, ← RingHom.coe_coe (MonoidAlgebra.lift R R Q 1), haug]
      simp
  have hmem := 𝔐.add_mem (hdiff x) hx𝔐
  rw [sub_add_cancel] at hmem
  exact h𝔐.ne_top (𝔐.eq_top_of_isUnit_mem hmem (hx.map _))

/-- **The group algebra of a `p`-group is local.** For a finite commutative `p`-group `Q` and a
local ring `R` in which `p` is not a unit, the group algebra `R[Q]` is a local ring. -/
theorem isLocalRing_of_isPGroup (hp : ¬IsUnit (p : R)) (hQ : IsPGroup p Q) :
    IsLocalRing (MonoidAlgebra R Q) :=
  have := isLocalHom_lift_one_of_isPGroup hp hQ
  (MonoidAlgebra.lift R R Q 1 : MonoidAlgebra R Q →+* R).domain_isLocalRing

end PGroup

end TauCeti.MonoidAlgebra
