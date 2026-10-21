/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Invariant.Free
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight

/-!
# Finite étale torsors under a finite group

Let a finite group `G` act on a commutative `A`-algebra `B` by `A`-algebra automorphisms. Then `B`
is a *finite étale `G`-torsor over `A`* (`TauCeti.Algebra.IsFiniteEtaleTorsor G A B`) if `B` is a
finite étale, faithfully flat `A`-algebra and the Galois map

  `B ⊗[A] B → (G → B)`,  `b ⊗ b' ↦ (b * g • b')_g`

(`TauCeti.MulSemiringAction.tensorToPi`) is bijective. Geometrically, `Spec B → Spec A` is a
torsor under the constant finite group scheme `G`: it is finite étale and surjective, and
`Spec B ×_{Spec A} Spec B` is the disjoint union of `|G|` copies of `Spec B`. Faithful flatness is
part of the definition; it excludes the zero algebra over a nonzero ring, which has a bijective
Galois map for every `G`. Over a field, the torsors are the nonzero finite étale algebras with
bijective Galois map, and those that are fields are exactly the finite Galois extensions with
Galois group `G`.

Finite étale torsors are the levels of the towers of finite étale covers used to split every
finite étale algebra over a ring and to build its universal cover, as in Scholze's construction of
the perfectoid cover of an analytic adic space by a tower of finite étale torsors.

## Main definitions

* `TauCeti.Algebra.IsFiniteEtaleTorsor G A B`: `B` is a finite étale `G`-torsor over `A`.

## Main results

* `TauCeti.Algebra.isFiniteEtaleTorsor_iff`: `B` is a finite étale `G`-torsor over `A` if and only
  if `A → B` is injective, `A` is the ring of invariants, and the action is free, i.e. for each
  `g ≠ 1` the elements `g • b - b` generate the unit ideal (Chase–Harrison–Rosenberg).
* `TauCeti.Algebra.IsFiniteEtaleTorsor.isInvariant`: the ring of invariants of a torsor is `A`.
* `TauCeti.Algebra.IsFiniteEtaleTorsor.isGaloisGroup`: over a nonzero ring, `G` is a Galois group
  of `B` over `A` in Mathlib's sense.
* `TauCeti.Algebra.IsFiniteEtaleTorsor.rankAtStalk_eq_card`: a torsor has constant rank `|G|`.
* `TauCeti.Algebra.IsFiniteEtaleTorsor.iff_field`: over a field, a torsor is a nonzero finite
  étale algebra with bijective Galois map.
* `TauCeti.Algebra.IsFiniteEtaleTorsor.iff_isGaloisGroup`,
  `TauCeti.Algebra.IsFiniteEtaleTorsor.iff_isGalois`: for a field extension `L / K`, `L` is a
  `G`-torsor over `K` if and only if `G` is a Galois group of `L / K`, if and only if `L / K` is
  Galois and `G` maps isomorphically onto `Gal(L / K)`.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, Theorem 1.3.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3 and the proof of Proposition 15.4.
-/

public section

open TensorProduct

namespace TauCeti.Algebra

variable (G A B : Type*) [Group G] [CommRing A] [CommRing B] [Algebra A B]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- `B` is a *finite étale `G`-torsor* over `A`: a finite étale, faithfully flat `A`-algebra whose
Galois map `B ⊗[A] B → (G → B)`, `b ⊗ b' ↦ (b * g • b')_g`, is bijective. Geometrically,
`Spec B → Spec A` is a torsor under the constant finite group scheme `G`. -/
class IsFiniteEtaleTorsor [Finite G] : Prop where
  etale : Algebra.Etale A B
  finite : Module.Finite A B
  faithfullyFlat : Module.FaithfullyFlat A B
  bijective_tensorToPi : Function.Bijective (MulSemiringAction.tensorToPi A B G)

variable {G A B} [Finite G]

namespace IsFiniteEtaleTorsor

/-- The ring of invariants of a finite étale torsor is the base ring. -/
instance isInvariant [h : IsFiniteEtaleTorsor G A B] : Algebra.IsInvariant A B G := by
  have := h.faithfullyFlat
  refine ⟨fun b hb ↦ ?_⟩
  -- An invariant `b` has `b ⊗ 1 = 1 ⊗ b`, because both have Galois image the constant function
  -- `b`, and faithfully flat descent puts such an element in the image of `A`.
  have htmul : b ⊗ₜ[A] (1 : B) = 1 ⊗ₜ[A] b :=
    h.bijective_tensorToPi.1 <| funext fun g ↦ by simp [hb g]
  obtain ⟨a, ha⟩ := (Algebra.IsEffective.of_faithfullyFlat (R := A) (S := B) b).mp
    (by simp [htmul])
  exact ⟨a, ha⟩

end IsFiniteEtaleTorsor

/-- **Chase–Harrison–Rosenberg.** `B` is a finite étale `G`-torsor over `A` if and only if
`A → B` is injective, `A` is the ring of invariants, and the action is free: for each `g ≠ 1` the
elements `g • b - b` generate the unit ideal of `B`. -/
theorem isFiniteEtaleTorsor_iff : IsFiniteEtaleTorsor G A B ↔
    FaithfulSMul A B ∧ Algebra.IsInvariant A B G ∧
      ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun b : B ↦ g • b - b) = ⊤ := by
  refine ⟨fun h ↦ ⟨?_, inferInstance,
    MulSemiringAction.tensorToPi_surjective_iff.mp h.bijective_tensorToPi.2⟩,
    fun ⟨_, _, hG⟩ ↦ ⟨MulSemiringAction.etale hG, MulSemiringAction.moduleFinite hG,
      MulSemiringAction.faithfullyFlat hG, MulSemiringAction.tensorToPi_bijective hG⟩⟩
  have := h.faithfullyFlat
  infer_instance

namespace IsFiniteEtaleTorsor

/-- Over the zero ring, the zero algebra is a finite étale torsor under every finite group. -/
instance (priority := 100) of_subsingleton [Subsingleton A] : IsFiniteEtaleTorsor G A B := by
  have : Subsingleton B := Module.subsingleton A B
  refine isFiniteEtaleTorsor_iff.mpr ⟨⟨fun {_ _} _ ↦ Subsingleton.elim _ _⟩,
    ⟨fun b _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- Over a nonzero ring, a finite étale torsor under `G` makes `G` a Galois group of `B` over `A`.
Over the zero ring this fails for every nontrivial `G`, whose action is then not faithful. -/
instance isGaloisGroup [Nontrivial A] [h : IsFiniteEtaleTorsor G A B] : IsGaloisGroup G A B := by
  -- The action is faithful: for a nonidentity element acting trivially, the differences
  -- `g • b - b` would generate the zero ideal rather than the unit ideal.
  obtain ⟨_, _, hG⟩ := isFiniteEtaleTorsor_iff.mp h
  have : Nontrivial B := (FaithfulSMul.algebraMap_injective A B).nontrivial
  refine ⟨⟨fun {g₁ g₂} hg ↦ ?_⟩, inferInstance, inferInstance⟩
  by_contra hne
  have hspan := hG (g₂⁻¹ * g₁) (by rwa [ne_eq, inv_mul_eq_one, eq_comm])
  have h0 : (Set.range fun b : B ↦ (g₂⁻¹ * g₁) • b - b) = {0} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨0, by simp⟩, ?_⟩
    rintro _ ⟨b, rfl⟩
    simp [mul_smul, hg b]
  rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hspan
  exact bot_ne_top hspan

/-- A finite étale `G`-torsor is finite projective of constant rank `|G|`. -/
theorem rankAtStalk_eq_card [h : IsFiniteEtaleTorsor G A B] (p : PrimeSpectrum A) :
    Module.rankAtStalk (R := A) B p = Nat.card G := by
  have := h.finite
  have := h.faithfullyFlat
  have := Fintype.ofFinite G
  -- Over a prime of `B` lying over `p`, the rank of `B` at `p` is the rank of
  -- `B ⊗[A] B ≃ (G → B)` over `B`.
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  have : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨q⟩
  let e : B ⊗[A] B ≃ₗ[B] (G → B) :=
    (AlgEquiv.ofBijective _ h.bijective_tensorToPi).toLinearEquiv
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_of_equiv e,
    Module.rankAtStalk_eq_finrank_of_free]
  simp [Nat.card_eq_fintype_card]

end IsFiniteEtaleTorsor

section Field

namespace IsFiniteEtaleTorsor

/-- Over a field, a finite étale `G`-torsor is a nonzero finite étale algebra with bijective Galois
map. The algebra may be disconnected, and the characteristic may divide `|G|`. -/
theorem iff_field (K : Type*) [Field K] [Algebra K B] [SMulCommClass G K B] :
    IsFiniteEtaleTorsor G K B ↔ Nontrivial B ∧ Module.Finite K B ∧ Algebra.Etale K B ∧
      Function.Bijective (MulSemiringAction.tensorToPi K B G) := by
  -- A nonzero module over a field is free, hence faithfully flat.
  refine ⟨fun h ↦ ?_, fun ⟨_, hfin, het, hbij⟩ ↦ ⟨het, hfin, inferInstance, hbij⟩⟩
  have := h.faithfullyFlat
  exact ⟨(FaithfulSMul.algebraMap_injective K B).nontrivial, h.finite, h.etale,
    h.bijective_tensorToPi⟩

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [MulSemiringAction G L]
  [SMulCommClass G K L]

/-- For a field extension `L / K`, `L` is a finite étale `G`-torsor over `K` exactly when `G` is a
Galois group of `L / K`. -/
theorem iff_isGaloisGroup : IsFiniteEtaleTorsor G K L ↔ IsGaloisGroup G K L := by
  -- A nonidentity element moves some `b`, and `g • b - b` is then a unit.
  refine ⟨fun _ ↦ inferInstance, fun h ↦ isFiniteEtaleTorsor_iff.mpr
    ⟨inferInstance, h.isInvariant, fun g hg ↦ ?_⟩⟩
  have := h.faithful
  obtain ⟨b, hb⟩ : ∃ b : L, g • b ≠ b := by
    by_contra! h'
    exact hg (eq_of_smul_eq_smul (α := L) fun b ↦ by rw [h', one_smul])
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨b, rfl⟩) (sub_ne_zero.mpr hb).isUnit

/-- For a field extension `L / K`, `L` is a finite étale `G`-torsor over `K` exactly when `L / K`
is Galois and the action identifies `G` with `Gal(L / K)`. -/
theorem iff_isGalois : IsFiniteEtaleTorsor G K L ↔
    IsGalois K L ∧ Function.Bijective (MulSemiringAction.toAlgAut G K L) := by
  rw [iff_isGaloisGroup]
  exact ⟨fun _ ↦ ⟨IsGaloisGroup.isGalois G K L, (IsGaloisGroup.mulEquivAlgEquiv G K L).bijective⟩,
    fun ⟨_, h⟩ ↦ .of_mulEquiv_algEquiv (MulEquiv.ofBijective _ h) fun _ _ ↦ rfl⟩

/-- A finite Galois extension `L / K` is a finite étale torsor under its Galois group. -/
instance of_isGalois (K L : Type*) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] : IsFiniteEtaleTorsor Gal(L/K) K L :=
  iff_isGaloisGroup.mpr inferInstance

end IsFiniteEtaleTorsor

end Field

end TauCeti.Algebra
