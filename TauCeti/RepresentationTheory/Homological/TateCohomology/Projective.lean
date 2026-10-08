/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
public import TauCeti.RepresentationTheory.NormSplit.BaseChange
import Mathlib.Algebra.CharP.Quotient
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.RepresentationTheory.NormSplit.PGroup

/-!
# Projective representations and cohomological triviality

Let `k` be a commutative ring and `G` a group. A representation `A` of `G` over `k` whose
`k[G]`-module is projective has vanishing Tate cohomology in every degree on every finite subgroup
of `G` (Serre, *Local Fields*, IX §5; Brown, *Cohomology of Groups*, VI §8). This is
the easy half of the theorem of Nakayama and Rim, which for `k = ℤ` characterizes the
cohomologically trivial `G`-modules of a finite group `G` as those of projective dimension at most
one over `ℤ[G]`.

The projection `Ind_⊥^G A → A` from the representation induced from the trivial subgroup is an
epimorphism, so a projective `A` is a retract of `Ind_⊥^G A`. The Tate cohomology of every finite
subgroup with coefficients in `Ind_⊥^G A` vanishes
(`TauCeti.TateCohomology.isZero_res_indBot`), hence so does that of its retract `A`.

Conversely, let `k` be an integral domain of characteristic zero in which every prime number is a
unit or generates a maximal ideal, for instance `ℤ`, `ℤ_[p]`, `ℤ_(p)` or a field of characteristic
zero, and let `G` be finite. A cohomologically trivial representation `A` of `G` over `k` whose
underlying `k`-module is projective (for instance free, of any rank) is a projective `k[G]`-module:
this is the lattice form of the theorem of Nakayama and Rim.

It suffices that the identity of `A` is a norm `∑ g, A.ρ g ∘ φ ∘ A.ρ g⁻¹`
(`Rep.moduleProjective_of_id_mem_range_norm_linHom`), and this may be checked on a Sylow
`p`-subgroup `P` for each prime `p` (`Representation.id_mem_range_norm_linHom_of_forall_prime`).
If `p` is a unit in `k`, the identity is `|P|⁻¹` times the norm of the identity. Otherwise
`F = k/pk` is a field of characteristic `p`. The vanishing of `Ĥ⁰(P, A)` and `Ĥ⁻¹(P, A)` gives the
vanishing of `Ĥ⁻¹(P, A/pA)` (`Rep.ker_norm_baseChange_le`), so the identity of `A/pA` is a norm
(`Representation.id_mem_range_norm_linHom_of_ker_norm_le`), and so is the identity of `A`
(`Representation.id_mem_range_norm_linHom_of_baseChange`).

## Main statements

* `Rep.isZero_res_of_projective`: if `A.ρ.asModule` is a projective
  `k[G]`-module, then `H-hat^n(S, A) = 0` for every finite subgroup `S` of `G` and every `n : ℤ`.
* `Rep.ker_norm_baseChange_le`: if `Ĥ⁰(G, A) = Ĥ⁻¹(G, A) = 0` and `p` is regular on `A`, then
  `Ĥ⁻¹(G, (k/pk) ⊗ A) = 0`, in the form `ker N ≤ I_G ((k/pk) ⊗ A)`.
* `Rep.projective_of_isZero_res`: over `k` as above, a cohomologically trivial representation of a
  finite group whose underlying `k`-module is projective is projective over `k[G]`.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §§3–5.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
* D. S. Rim, *Modules over finite groups*, Ann. of Math. 69 (1959).
-/

public section

universe u

open CategoryTheory Limits Rep TauCeti.TateCohomology
open scoped TensorProduct

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- **Projective modules are cohomologically trivial.** If the `k[G]`-module of a representation
`A` is projective, then the Tate cohomology of every finite subgroup `S` of `G` with coefficients
in `A` vanishes in every degree. -/
theorem isZero_res_of_projective (A : Rep k G)
    [Module.Projective (MonoidAlgebra k G) A.ρ.asModule] (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype A) n) := by
  have : Projective A := by
    rwa [← equivalenceModuleMonoidAlgebra.map_projective_iff, ← IsProjective.iff_projective]
  -- `A` is a retract of `Ind_⊥^G A`, whose Tate cohomology on `S` vanishes.
  have h := (Retract.mk _ _ (Projective.factorThru_comp (𝟙 A) (indBotCounit A))).map
    (resFunctor (k := k) S.subtype) |>.map (tateCohomologyFunctor n)
  rw [IsZero.iff_id_eq_zero, ← h.retract,
    (TauCeti.TateCohomology.isZero_res_indBot S A.V n).eq_zero_of_tgt h.i, zero_comp]

/-- **`Ĥ⁻¹` modulo `p`.** If `Ĥ⁰(G, A)` and `Ĥ⁻¹(G, A)` vanish and multiplication by `p` is
injective on `A`, then every vector of `(k/pk) ⊗ A` of norm zero lies in the augmentation
submodule; that is, `Ĥ⁻¹(G, (k/pk) ⊗ A) = 0`. -/
theorem ker_norm_baseChange_le [Fintype G] (A : Rep k G) (p : k)
    (hp : ∀ v : A.V, p • v = 0 → v = 0) (h0 : IsZero (tateCohomology A 0))
    (h1 : IsZero (tateCohomology A (-1))) :
    LinearMap.ker (A.ρ.baseChange (k ⧸ Ideal.span {p})).norm ≤
      Representation.Coinvariants.ker (A.ρ.baseChange (k ⧸ Ideal.span {p})) := by
  classical
  set Q := k ⧸ Ideal.span {p}
  set ρQ := A.ρ.baseChange Q
  let red : A.V →ₗ[k] Q ⊗[k] A.V := TensorProduct.mk k Q A.V 1
  have hred_eq_zero (v : A.V) : red v = 0 ↔ ∃ w : A.V, p • w = v :=
    TensorProduct.one_tmul_eq_zero_iff_exists_smul_eq p v
  have hredρ (g : G) (v : A.V) : ρQ g (red v) = red (A.ρ g v) := by simp [ρQ, red]
  have hredN (v : A.V) : ρQ.norm (red v) = red (A.ρ.norm v) := by
    simp [Representation.norm, hredρ]
  intro y hy
  obtain ⟨x, rfl⟩ : ∃ x, red x = y := TensorProduct.exists_one_tmul_eq (Ideal.span {p}) y
  rw [LinearMap.mem_ker, hredN, hred_eq_zero] at hy
  obtain ⟨z, hz⟩ := hy
  -- `z` is invariant, hence a norm `N w`, and `x - p w` has norm zero.
  have hzinv : z ∈ A.ρ.invariants := fun g ↦ by
    refine sub_eq_zero.1 (hp _ ?_)
    rw [smul_sub, ← map_smul, hz, sub_eq_zero]
    exact A.ρ.self_norm_apply g x
  have := ModuleCat.subsingleton_of_isZero h0
  obtain ⟨w, hw⟩ := (H0π_eq_zero_iff ⟨z, hzinv⟩).1 (Subsingleton.elim _ _)
  have hxw : x - p • w ∈ LinearMap.ker A.ρ.norm := by
    rw [LinearMap.mem_ker, map_sub, map_smul, ← hz, hw, Submodule.subtype_apply, sub_self]
  have := ModuleCat.subsingleton_of_isZero h1
  have hmem := (HNegOneπ_eq_zero_iff ⟨x - p • w, hxw⟩).1 (Subsingleton.elim _ _)
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hmem
  -- Reduction carries the augmentation submodule of `A` into that of `(k/pk) ⊗ A`.
  have hcoinv : Representation.Coinvariants.ker A.ρ ≤
      ((Representation.Coinvariants.ker ρQ).restrictScalars k).comap red :=
    Submodule.span_le.2 fun _ ⟨⟨g, v⟩, hv⟩ ↦ by
      simpa [← hv, ← hredρ] using Representation.Coinvariants.sub_mem_ker (ρ := ρQ) g (red v)
  have := hcoinv hmem
  rwa [Submodule.mem_comap, map_sub, (hred_eq_zero _).2 ⟨w, rfl⟩, sub_zero] at this

/-- **Nakayama–Rim, lattice form** (Serre, *Local Fields*, IX §§3–5; Rim, Ann. of Math. 69
(1959)). Over an integral domain of characteristic zero in which every prime number is a unit or
generates a maximal ideal (for instance `ℤ`, `ℤ_[p]` or `ℤ_(p)`), a cohomologically trivial
representation of a finite group whose underlying `k`-module is projective — for instance free, of
any rank — is projective over `k[G]`. -/
theorem projective_of_isZero_res [Finite G] [IsDomain k] [CharZero k]
    (hk : ∀ p : ℕ, p.Prime → IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal)
    (A : Rep k G) [Module.Projective k A.V]
    (hA : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      IsZero (tateCohomology (res S.subtype A) n)) :
    Module.Projective (MonoidAlgebra k G) A.ρ.asModule := by
  classical
  have := Fintype.ofFinite G
  refine Rep.moduleProjective_of_id_mem_range_norm_linHom A
    (A.ρ.id_mem_range_norm_linHom_of_forall_prime fun p hp _ ↦ ?_)
  have := Fact.mk hp
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  refine ⟨P, inferInstance, P.not_dvd_index, ?_⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have hcard : Fintype.card P = p ^ m := by rw [← hm, Nat.card_eq_fintype_card]
  -- The conjugation action of `G` restricted to `P` is, by definition, the conjugation action
  -- of the restriction `A.ρ.comp P.subtype`, the form the norm-splitting lemmas are stated in.
  suffices LinearMap.id ∈ LinearMap.range (Representation.linHom (A.ρ.comp (P : Subgroup G).subtype)
      (A.ρ.comp (P : Subgroup G).subtype)).norm from this
  rcases hk p hp with hunit | hmax
  · -- `|P|` is a unit, and the identity is the norm of `|P|⁻¹ • id`.
    obtain ⟨u, hu⟩ := hunit.pow m
    refine ⟨(↑u⁻¹ : k) • LinearMap.id, LinearMap.ext fun x ↦ ?_⟩
    rw [Representation.norm_linHom_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, map_smul, Representation.self_inv_apply,
      Finset.sum_const, Finset.card_univ, hcard, ← Nat.cast_smul_eq_nsmul k, smul_smul,
      Nat.cast_pow, ← hu, Units.mul_inv, one_smul]
  · -- `k/pk` is a field of characteristic `p`.
    let := Ideal.Quotient.field (Ideal.span {(p : k)})
    have : CharP (k ⧸ Ideal.span {(p : k)}) p :=
      CharP.quotient k p (mem_nonunits_iff.2 fun hu ↦ hmax.ne_top
        (Ideal.span_singleton_eq_top.2 hu))
    have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hreg (v : A.V) (hv : (p : k) • v = 0) : v = 0 := (smul_eq_zero.1 hv).resolve_left hp0
    exact Representation.id_mem_range_norm_linHom_of_baseChange (A.ρ.comp (P : Subgroup G).subtype)
      hcard hreg
      (Representation.id_mem_range_norm_linHom_of_ker_norm_le p P.isPGroup' _
        (ker_norm_baseChange_le (res (P : Subgroup G).subtype A) (p : k) hreg (hA P 0)
          (hA P (-1))))

end Rep
