/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.RepresentationTheory.Intertwining
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Residually disjoint representations

Let `A` be a commutative local ring with residue field `κ`, and let `ρ` and `σ` be representations
of a monoid `G` on finite free `A`-modules `V` and `W`. Following Skinner–Urban, `ρ` and `σ` are
*residually disjoint* if some element `x` of the group algebra `A[G]` acts on `V` and on `W` with
characteristic polynomials whose reductions to `κ[X]` are coprime.

Skinner and Urban's Lemma 4.1.3 turns residual disjointness into a separating element: some
`e ∈ A[G]` acts as the identity on `V` and as zero on `W`, and then `1 - e` acts as zero on `V`
and as the identity on `W`. The converse holds as well (take `x = e`), so residual disjointness is
exactly the existence of such a separating element of `A[G]`. Consequently:

* a representation `ρ` is residually disjoint from each of the finitely many representations
  `ρ j` exactly when one element of `A[G]` acts as the identity on `ρ` and kills every `ρ j`;
* residually disjoint representations admit no nonzero intertwining map, so a nonzero
  representation is never residually disjoint from itself;
* the one-dimensional representations of two characters `χ ψ : G →* Aˣ` are residually disjoint
  exactly when the reductions of `χ` and `ψ` to `κ` differ. This is the form of Skinner–Urban's
  hypothesis that `χ` and `ν χ⁻ᶜ` have distinct reductions in their lattice construction.

## Conventions

The characteristic polynomial here is Mathlib's monic `det (X - ρ x)`. Skinner and Urban write
`Ch(ρ, x, T) = det (1 - T ρ x)`, its reciprocal; with that convention `x = 0` would have
characteristic polynomial `1` on every representation, so every two representations would be
residually disjoint and Lemma 4.1.3 would fail (two copies of the same nonzero representation
admit no separating element). The monic convention is the one under which their proof, through
the Cayley–Hamilton theorem, is correct. No Henselian hypothesis is needed: coprimality of monic
polynomials lifts from `κ[X]` to `A[X]` over any local ring.

## Main definitions

* `Representation.IsResiduallyDisjoint`: residual disjointness of two representations over a
  local ring.

## Main results

* `Representation.isResiduallyDisjoint_iff_exists_asAlgebraHom`: residual disjointness is the
  existence of `e ∈ A[G]` acting as the identity on the first representation and as zero on the
  second (Skinner–Urban, Lemma 4.1.3, and its converse).
* `Representation.forall_ne_isResiduallyDisjoint_iff_exists_asAlgebraHom`: the projector
  separating one member of a finite family from all the others.
* `Representation.IsResiduallyDisjoint.intertwiningMap_eq_zero`,
  `Representation.not_isResiduallyDisjoint_self`: residually disjoint representations have no
  nonzero intertwining maps.
* `Representation.isResiduallyDisjoint_ofLinearCharacter_iff`: two characters are residually
  disjoint exactly when their reductions differ.

## References

* C. Skinner, E. Urban, *The Iwasawa main conjectures for GL₂*, Invent. Math. 195 (2014),
  §4.1.2, Lemma 4.1.3 and §4.2.3.
-/

public section

open Module Polynomial IsLocalRing

namespace Representation

variable {A G V W : Type*} [CommRing A] [IsLocalRing A] [Monoid G]
  [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
  [AddCommGroup W] [Module A W] [Module.Free A W] [Module.Finite A W]

/-- Two representations `ρ` and `σ` over a local ring `A` are **residually disjoint** if some
element `x` of the group algebra `A[G]` acts on them with characteristic polynomials whose
reductions modulo the maximal ideal of `A` are coprime (Skinner–Urban, §4.1.2, with the monic
characteristic polynomial `det (X - ρ x)` in place of its reciprocal). -/
def IsResiduallyDisjoint (ρ : Representation A G V) (σ : Representation A G W) : Prop :=
  ∃ x : MonoidAlgebra A G, IsCoprime ((ρ.asAlgebraHom x).charpoly.map (residue A))
    ((σ.asAlgebraHom x).charpoly.map (residue A))

variable {ρ : Representation A G V} {σ : Representation A G W}

/-- The defining condition of residual disjointness: some `x ∈ A[G]` acts on `ρ` and on `σ` with
characteristic polynomials whose reductions modulo the maximal ideal are coprime. -/
theorem isResiduallyDisjoint_iff : ρ.IsResiduallyDisjoint σ ↔
    ∃ x : MonoidAlgebra A G, IsCoprime ((ρ.asAlgebraHom x).charpoly.map (residue A))
      ((σ.asAlgebraHom x).charpoly.map (residue A)) :=
  Iff.rfl

/-- Residual disjointness is symmetric. -/
@[symm]
theorem IsResiduallyDisjoint.symm (h : ρ.IsResiduallyDisjoint σ) : σ.IsResiduallyDisjoint ρ :=
  let ⟨x, hx⟩ := h
  ⟨x, hx.symm⟩

/-- Residual disjointness is symmetric. -/
theorem isResiduallyDisjoint_comm : ρ.IsResiduallyDisjoint σ ↔ σ.IsResiduallyDisjoint ρ :=
  ⟨.symm, .symm⟩

/-- **Skinner–Urban, Lemma 4.1.3.** If `ρ` and `σ` are residually disjoint, some `e ∈ A[G]` acts
as the identity on `ρ` and as zero on `σ`; then `1 - e` acts as zero on `ρ` and as the identity
on `σ`. -/
theorem IsResiduallyDisjoint.exists_asAlgebraHom (h : ρ.IsResiduallyDisjoint σ) :
    ∃ e : MonoidAlgebra A G, ρ.asAlgebraHom e = 1 ∧ σ.asAlgebraHom e = 0 := by
  obtain ⟨x, hx⟩ := h
  have hres : residue A = Ideal.Quotient.mk (maximalIdeal A) := RingHom.ext residue_def
  rw [hres] at hx
  -- The coprimality of the residual characteristic polynomials lifts to `A[X]`.
  obtain ⟨a, b, hab⟩ := Polynomial.isCoprime_of_isCoprime_map (ringJacobson_eq_maximalIdeal A).ge
    (LinearMap.charpoly_monic _) hx
  refine ⟨aeval x (b * (σ.asAlgebraHom x).charpoly), ?_, ?_⟩
  · rw [← aeval_algHom_apply, ← sub_eq_of_eq_add' hab.symm, map_sub, map_one, map_mul,
      LinearMap.aeval_self_charpoly, mul_zero, sub_zero]
  · rw [← aeval_algHom_apply, map_mul, LinearMap.aeval_self_charpoly, mul_zero]

/-- An element of `A[G]` acting as the identity on `ρ` and as zero on `σ` witnesses residual
disjointness: its characteristic polynomials `(X - 1) ^ m` and `X ^ n` are coprime. -/
theorem isResiduallyDisjoint_of_asAlgebraHom {e : MonoidAlgebra A G}
    (hρ : ρ.asAlgebraHom e = 1) (hσ : σ.asAlgebraHom e = 0) : ρ.IsResiduallyDisjoint σ := by
  refine ⟨e, ?_⟩
  rw [hρ, hσ]
  simp only [LinearMap.charpoly_one, LinearMap.charpoly_zero, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  refine IsCoprime.pow ?_
  simpa using isCoprime_X_sub_C_of_isUnit_sub (R := ResidueField A) (a := 1) (b := 0) (by simp)

/-- **Residual disjointness is separation by the group algebra.** Two representations over a
local ring are residually disjoint if and only if some `e ∈ A[G]` acts as the identity on the
first and as zero on the second (Skinner–Urban, Lemma 4.1.3, and its converse). -/
theorem isResiduallyDisjoint_iff_exists_asAlgebraHom :
    ρ.IsResiduallyDisjoint σ ↔
      ∃ e : MonoidAlgebra A G, ρ.asAlgebraHom e = 1 ∧ σ.asAlgebraHom e = 0 :=
  ⟨IsResiduallyDisjoint.exists_asAlgebraHom, fun ⟨_, hρ, hσ⟩ ↦
    isResiduallyDisjoint_of_asAlgebraHom hρ hσ⟩

/-- **Projectors for a finite family.** A representation `ρ i` is residually disjoint from every
other member of a finite family `ρ` exactly when one element of `A[G]` acts as the identity on
`ρ i` and as zero on every `ρ j` with `j ≠ i`. -/
theorem forall_ne_isResiduallyDisjoint_iff_exists_asAlgebraHom {ι : Type*} [Finite ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module A (V i)] [∀ i, Module.Free A (V i)]
    [∀ i, Module.Finite A (V i)] (ρ : ∀ i, Representation A G (V i)) (i : ι) :
    (∀ j ≠ i, (ρ i).IsResiduallyDisjoint (ρ j)) ↔
      ∃ e : MonoidAlgebra A G, (ρ i).asAlgebraHom e = 1 ∧ ∀ j ≠ i, (ρ j).asAlgebraHom e = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨e, hi, hj⟩ j hji ↦ isResiduallyDisjoint_of_asAlgebraHom hi (hj j hji)⟩
  have : ∀ j, ∃ e : MonoidAlgebra A G,
      (ρ i).asAlgebraHom e = 1 ∧ (j ≠ i → (ρ j).asAlgebraHom e = 0) := fun j ↦ by
    by_cases hji : j = i
    · exact ⟨1, map_one _, fun hne ↦ absurd hji hne⟩
    · obtain ⟨e, hi, hj⟩ := (h j hji).exists_asAlgebraHom
      exact ⟨e, hi, fun _ ↦ hj⟩
  choose f hfi hfj using this
  have := Fintype.ofFinite ι
  -- The product of the separating elements of the pairs `(i, j)` separates `ρ i` from all `ρ j`.
  refine ⟨(Finset.univ.toList.map f).prod, ?_, fun j hji ↦ ?_⟩
  · rw [map_list_prod, List.map_map]
    exact List.prod_eq_one fun _ hx ↦ by
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      exact hfi k
  · rw [map_list_prod, List.map_map]
    exact List.prod_eq_zero (List.mem_map.2 ⟨j, by simp, hfj j hji⟩)

/-- Residually disjoint representations admit no nonzero intertwining map. -/
theorem IsResiduallyDisjoint.intertwiningMap_eq_zero (h : ρ.IsResiduallyDisjoint σ)
    (f : IntertwiningMap ρ σ) : f = 0 := by
  obtain ⟨e, hρ, hσ⟩ := h.exists_asAlgebraHom
  refine IntertwiningMap.ext (LinearMap.ext fun v ↦ ?_)
  have hv := f.apply_asAlgebraHom e v
  rw [hρ, hσ] at hv
  simpa using hv

/-- A nonzero representation is not residually disjoint from itself. -/
theorem not_isResiduallyDisjoint_self [Nontrivial V] (ρ : Representation A G V) :
    ¬ρ.IsResiduallyDisjoint ρ := fun h ↦ by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact hv (by simpa using congr($(h.intertwiningMap_eq_zero (IntertwiningMap.id ρ)) v))

/-- **Residual disjointness of characters.** The one-dimensional representations of two
characters `χ ψ : G →* Aˣ` are residually disjoint if and only if the reductions of `χ` and `ψ`
modulo the maximal ideal differ at some `g : G`. -/
theorem isResiduallyDisjoint_ofLinearCharacter_iff {χ ψ : G →* Aˣ} :
    (ofLinearCharacter χ).IsResiduallyDisjoint (ofLinearCharacter ψ) ↔
      ∃ g, residue A (χ g) ≠ residue A (ψ g) := by
  rw [isResiduallyDisjoint_iff_exists_asAlgebraHom]
  constructor
  · rintro ⟨e, hχ, hψ⟩
    by_contra! h
    -- If the reductions of `χ` and `ψ` agree on `G`, the scalars `1` and `0` by which `e` acts
    -- agree modulo the maximal ideal, a contradiction.
    have key : (Algebra.ofId A (ResidueField A)).comp
          (MonoidAlgebra.lift A A G ((Units.coeHom A).comp χ)) =
        (Algebra.ofId A (ResidueField A)).comp
          (MonoidAlgebra.lift A A G ((Units.coeHom A).comp ψ)) :=
      (MonoidAlgebra.lift A (ResidueField A) G).symm.injective
        (MonoidHom.ext fun g ↦ by simpa using h g)
    have h1 := LinearMap.congr_fun hχ 1
    have h0 := LinearMap.congr_fun hψ 1
    rw [asAlgebraHom_ofLinearCharacter_apply, mul_one] at h1 h0
    simpa [h1, h0] using congr($key e)
  · rintro ⟨g, hg⟩
    obtain ⟨u, hu⟩ : IsUnit ((χ g : A) - ψ g) :=
      (residue_ne_zero_iff_isUnit _).1 (by simpa [sub_eq_zero])
    refine ⟨(↑u⁻¹ : A) • (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 (ψ g : A)), ?_, ?_⟩ <;>
      refine LinearMap.ext_ring ?_ <;> rw [asAlgebraHom_ofLinearCharacter_apply] <;> simp [← hu]

end Representation
