/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Sylow
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Coinduced
public import TauCeti.RepresentationTheory.NormSplit.BaseChange
import Mathlib.Algebra.CharP.Quotient
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.RepresentationTheory.Coinvariants
import TauCeti.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.NormSplit.PGroup
import TauCeti.RepresentationTheory.Homological.TateCohomology.HomologySequence
import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# Projectivity and cohomological triviality

Let `k` be a commutative ring and `G` a group. A representation `A` of `G` over `k` whose
`k[G]`-module is projective has vanishing Tate cohomology in every degree on every finite subgroup
of `G` (Serre, *Local Fields*, IX §5; Brown, *Cohomology of Groups*, VI §8). More generally, so
does a representation of projective dimension at most one over `k[G]`. This is the easy half of
the theorem of Nakayama and Rim, which for `k = ℤ` characterizes the cohomologically trivial
`G`-modules of a finite group `G` as those of projective dimension at most one over `ℤ[G]`.
Both statements survive tensoring, with the diagonal action, by an arbitrary representation `M`:
`M ⊗ A` is cohomologically trivial for projective `A`, and for `A` with a projective resolution
`0 → P₁ → P₀ → A → 0` of length one as soon as `M ⊗ P₁ → M ⊗ P₀` stays injective. This is the
form in which cohomological triviality enters the Tate–Nakayama generalization of Tate's theorem.

The projection `Ind_⊥^G A → A` from the representation induced from the trivial subgroup is an
epimorphism, so a projective `A` is a retract of `Ind_⊥^G A`, and `M ⊗ A` is a retract of
`M ⊗ Ind_⊥^G A`. The Tate cohomology of every finite subgroup with coefficients in
`M ⊗ Ind_⊥^G A` vanishes (`TauCeti.TateCohomology.isZero_tensor_indBot`, after restricting the
induced module to the subgroup), hence so does that of its retract `M ⊗ A`; for `M` the unit
representation this is the statement for `A` itself. If `0 → P₁ → P₀ → A → 0` is exact with `P₀`
and `P₁` projective, the Tate cohomology of `A` sits in the long exact sequence between that of
`P₀` and that of `P₁`, both of which vanish; the same holds after tensoring with `M` whenever the
tensored sequence is still short exact.

Conversely, let `k` be an integral domain of characteristic zero in which every prime number is a
unit or generates a maximal ideal, for instance `ℤ`, `ℤ_[p]`, `ℤ_(p)` or a field of characteristic
zero, and let `G` be finite. A cohomologically trivial representation `A` of `G` over `k` whose
underlying `k`-module is projective (for instance free, of any rank) is a projective `k[G]`-module:
this is the lattice form of the theorem of Nakayama and Rim.

It suffices that the identity of `A` is a norm `∑ g, A.ρ g ∘ φ ∘ A.ρ g⁻¹`
(`Rep.moduleProjective_of_id_mem_range_norm_linHom`), and this may be checked on a Sylow
`p`-subgroup `P` for each prime `p` (`Representation.id_mem_range_norm_linHom_of_forall_prime`).
If `p` is a unit in `k`, the identity is `|P|⁻¹` times the norm of the identity. Otherwise
`F = k/pk` is a field of characteristic `p`. The vanishing of `H_Tate⁰(P, A)` and
`H_Tate⁻¹(P, A)` gives the vanishing of `H_Tate⁻¹(P, A/pA)`
(`Rep.ker_norm_baseChange_le_coinvariantsKer`), so the identity of `A/pA` is a norm
(`Representation.id_mem_range_norm_linHom_of_ker_norm_le`), and so is the identity of `A`
(`Representation.id_mem_range_norm_linHom_of_baseChange`). Only primes dividing `|G|`, and only
the degrees `0` and `-1` on one Sylow subgroup for each of them, are used
(`Rep.projective_of_isZero_res_sylow`).

## Main statements

* `Rep.isZero_res_tensor_of_projective`: if `P.ρ.asModule` is a projective `k[G]`-module, then
  `H-hat^n(S, M ⊗ P) = 0` for every representation `M`, every finite subgroup `S` of `G` and every
  `n : ℤ`.
* `Rep.isZero_res_of_projective`: if `A.ρ.asModule` is a projective
  `k[G]`-module, then `H-hat^n(S, A) = 0` for every finite subgroup `S` of `G` and every `n : ℤ`.
* `Rep.ker_norm_baseChange_le_coinvariantsKer`: if `H_Tate⁰(G, A) = H_Tate⁻¹(G, A) = 0` and `p`
  is regular on `A`, then `H_Tate⁻¹(G, (k/pk) ⊗ A) = 0`, in the form `ker N ≤ I_G ((k/pk) ⊗ A)`.
* `Rep.projective_of_isZero_res_sylow`: a representation of a finite group on a projective
  `k`-module is projective over `k[G]` if, for each prime `p` dividing `|G|`, either `p` is a unit
  in `k`, or `pk` is maximal and `H_Tate⁰` and `H_Tate⁻¹` vanish on a Sylow `p`-subgroup.
* `Rep.projective_of_isZero_res`: over `k` as above, a cohomologically trivial representation of a
  finite group whose underlying `k`-module is projective is projective over `k[G]`.
* `Rep.isZero_res_of_exact`: the same vanishing when `A.ρ.asModule` has a projective resolution
  `0 → P₁ → P₀ → A → 0` of length one.
* `Rep.isZero_res_tensor_of_shortExact`: `H-hat^n(S, M ⊗ A) = 0` when `A` has a projective
  resolution `0 → P₁ → P₀ → A → 0` of length one with `M ⊗ P₁ → M ⊗ P₀` injective.

## References

* J.-P. Serre, *Local Fields*, Chapter IX, §§3–5.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §8.
* D. S. Rim, *Modules over finite groups*, Ann. of Math. 69 (1959).
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory Rep TauCeti.TateCohomology
open scoped TensorProduct

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- **Tensoring with a projective module gives a cohomologically trivial module.** If the
`k[G]`-module of a representation `P` is projective, then for every representation `M` the Tate
cohomology of every finite subgroup `S` of `G` with coefficients in `M ⊗ P` vanishes in every
degree. -/
theorem isZero_res_tensor_of_projective (M P : Rep k G)
    [Module.Projective (MonoidAlgebra k G) P.ρ.asModule] (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype (M ⊗ P)) n) := by
  have : Projective P := by
    rwa [← equivalenceModuleMonoidAlgebra.map_projective_iff, ← IsProjective.iff_projective]
  -- `M ⊗ P` is a retract of `M ⊗ Ind_⊥^G P`, whose Tate cohomology on `S` vanishes.
  have h := (((Retract.mk _ _ (Projective.factorThru_comp (𝟙 P) (indBotCounit P))).map
    (tensorLeft M)).map (resFunctor (k := k) S.subtype)).map (tateCohomologyFunctor n)
  -- The restriction of `Ind_⊥^G P` to `S` is induced from the trivial subgroup of `S`.
  let e := whiskerLeftIso (res S.subtype M) (resIndBotIso S P.V)
  have h₀ : IsZero (tateCohomology (res S.subtype (M ⊗ indBot k G P.V)) n) :=
    (isZero_tensor_indBot (G := S) (G ⧸ S →₀ P.V) (res S.subtype M) n).of_iso
      ((tateCohomologyFunctor n).mapIso e)
  exact (IsZero.iff_id_eq_zero _).2
    (h.retract.symm.trans (by rw [h₀.eq_zero_of_tgt h.i, zero_comp]))

/-- **Projective modules are cohomologically trivial.** If the `k[G]`-module of a representation
`A` is projective, then the Tate cohomology of every finite subgroup `S` of `G` with coefficients
in `A` vanishes in every degree. -/
theorem isZero_res_of_projective (A : Rep k G)
    [Module.Projective (MonoidAlgebra k G) A.ρ.asModule] (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype A) n) :=
  (isZero_res_tensor_of_projective (𝟙_ (Rep k G)) A S n).of_iso
    ((tateCohomologyFunctor n).mapIso ((resFunctor S.subtype).mapIso (λ_ A).symm))

/-- **`H_Tate⁻¹` modulo `p`.** If `H_Tate⁰(G, A)` and `H_Tate⁻¹(G, A)` vanish and multiplication
by `p` is injective on `A`, then every vector of `(k/pk) ⊗ A` of norm zero lies in the augmentation
submodule; that is, `H_Tate⁻¹(G, (k/pk) ⊗ A) = 0`. -/
theorem ker_norm_baseChange_le_coinvariantsKer [Fintype G] (A : Rep k G) (p : k)
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
    Submodule.map_le_iff_le_comap.mp
      (Representation.coinvariantsKer_map_le A.ρ (ρ' := ρQ) id red
        fun g v ↦ (hredρ g v).symm)
  have := hcoinv hmem
  rwa [Submodule.mem_comap, map_sub, (hred_eq_zero _).2 ⟨w, rfl⟩, sub_zero] at this

/-- **Nakayama–Rim, Sylow form** (Serre, *Local Fields*, IX §§3–5; Rim, Ann. of Math. 69 (1959)).
Let `k` be a commutative ring, `G` a finite group, and `A` a representation of `G` on a
projective `k`-module. Suppose that for each prime `p` dividing `|G|` some Sylow `p`-subgroup `P`
satisfies: `p` is a unit in `k`, or `pk` is a maximal ideal, multiplication by `p` is injective
on `A`, and `H_Tate⁰(P, A) = H_Tate⁻¹(P, A) = 0`. Then `A` is projective over `k[G]`. -/
theorem projective_of_isZero_res_sylow [Finite G]
    (A : Rep k G) [Module.Projective k A.V]
    (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → ∃ (P : Sylow p G) (_ : Fintype P),
      IsUnit (p : k) ∨ (Ideal.span {(p : k)}).IsMaximal ∧
        (∀ v : A.V, (p : k) • v = 0 → v = 0) ∧
        IsZero (tateCohomology (res (P : Subgroup G).subtype A) 0) ∧
        IsZero (tateCohomology (res (P : Subgroup G).subtype A) (-1))) :
    Module.Projective (MonoidAlgebra k G) A.ρ.asModule := by
  classical
  have := Fintype.ofFinite G
  refine Rep.moduleProjective_of_id_mem_range_norm_linHom A
    (A.ρ.id_mem_range_norm_linHom_of_forall_prime fun p hp hpG ↦ ?_)
  have := Fact.mk hp
  obtain ⟨P, _, hP⟩ := h p hp (by rwa [Nat.card_eq_fintype_card])
  refine ⟨P, inferInstance, P.not_dvd_index, ?_⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 P.isPGroup'
  have hcard : Fintype.card P = p ^ m := by rw [← hm, Nat.card_eq_fintype_card]
  -- The conjugation action of `G` restricted to `P` is, by definition, the conjugation action
  -- of the restriction `A.ρ.comp P.subtype`, the form the norm-splitting lemmas are stated in.
  suffices LinearMap.id ∈ LinearMap.range (Representation.linHom (A.ρ.comp (P : Subgroup G).subtype)
      (A.ρ.comp (P : Subgroup G).subtype)).norm from this
  rcases hP with hunit | ⟨hmax, hreg, h0, h1⟩
  · -- When `|P|` is a unit, the norm maps onto the invariant endomorphisms.
    have hunitCard : IsUnit (Fintype.card P : k) := by
      simpa only [hcard, Nat.cast_pow] using hunit.pow m
    let := hunitCard.invertible
    rw [Representation.range_norm_eq_invariants]
    intro g
    ext x
    simp only [Representation.linHom_apply, LinearMap.comp_apply, LinearMap.id_apply]
    exact Representation.self_inv_apply _ g x
  · -- `k/pk` is a field of characteristic `p`.
    let := Ideal.Quotient.field (Ideal.span {(p : k)})
    have : CharP (k ⧸ Ideal.span {(p : k)}) p :=
      CharP.quotient k p (mem_nonunits_iff.2 fun hu ↦ hmax.ne_top
        (Ideal.span_singleton_eq_top.2 hu))
    exact Representation.id_mem_range_norm_linHom_of_baseChange (A.ρ.comp (P : Subgroup G).subtype)
      hcard hreg
      (Representation.id_mem_range_norm_linHom_of_ker_norm_le p P.isPGroup' _
        (ker_norm_baseChange_le_coinvariantsKer (res (P : Subgroup G).subtype A) (p : k) hreg h0
          h1))

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
    Module.Projective (MonoidAlgebra k G) A.ρ.asModule :=
  projective_of_isZero_res_sylow A fun p hp _ ↦
    have := Fact.mk hp
    let P : Sylow p G := Classical.arbitrary _
    letI : Fintype P := .ofFinite P
    have hp0 : (p : k) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hreg (v : A.V) (hv : (p : k) • v = 0) : v = 0 :=
      (smul_eq_zero.1 hv).resolve_left hp0
    ⟨P, inferInstance, (hk p hp).imp_right fun hmax ↦ ⟨hmax, hreg, hA P 0, hA P (-1)⟩⟩

/-- **Projective dimension at most one implies cohomological triviality.** Let
`0 → P₁ → P₀ → A → 0` be an exact sequence of `k[G]`-modules with `P₀` and `P₁` projective. Then
the Tate cohomology of every finite subgroup `S` of `G` with coefficients in `A` vanishes in every
degree. -/
theorem isZero_res_of_exact (A : Rep k G) {P₀ P₁ : Type u}
    [AddCommGroup P₀] [Module (MonoidAlgebra k G) P₀] [Module.Projective (MonoidAlgebra k G) P₀]
    [AddCommGroup P₁] [Module (MonoidAlgebra k G) P₁] [Module.Projective (MonoidAlgebra k G) P₁]
    {d : P₁ →ₗ[MonoidAlgebra k G] P₀} {q : P₀ →ₗ[MonoidAlgebra k G] A.ρ.asModule}
    (hd : Function.Injective d) (hdq : Function.Exact d q) (hq : Function.Surjective q)
    (S : Subgroup G) [Fintype S] (n : ℤ) :
    IsZero (tateCohomology (res S.subtype A) n) := by
  -- Carry the sequence of `k[G]`-modules to representations of `G`, then restrict to `S`.
  have hT := ((ModuleCat.shortComplex_shortExact
    (ModuleCat.shortComplexOfCompEqZero d q hdq.linearMap_comp_eq_zero) hdq hd hq).map_of_exact
      ofModuleMonoidAlgebra).map_of_exact (resFunctor S.subtype)
  -- The representation attached to a projective `k[G]`-module is cohomologically trivial.
  have hP (M : ModuleCat (MonoidAlgebra k G)) [Module.Projective (MonoidAlgebra k G) M] (m : ℤ) :
      IsZero (tateCohomology (res S.subtype (ofModuleMonoidAlgebra.obj M)) m) :=
    have : Module.Projective (MonoidAlgebra k G) (ofModuleMonoidAlgebra.obj M).ρ.asModule :=
      .of_equiv (equivalenceModuleMonoidAlgebra.counitIso.app M).toLinearEquiv.symm
    isZero_res_of_projective _ S m
  -- The terms of `hT` are, by definition of `ShortComplex.map`, the restrictions of the
  -- representations attached to `P₁`, `P₀` and `A.ρ.asModule`; the last is isomorphic to `A`.
  exact (TauCeti.TateCohomology.isZero_X₃_of_isZero_X₂_of_isZero_X₁ hT n (n + 1) rfl
    (hP (.of _ P₀) n) (hP (.of _ P₁) (n + 1))).of_iso
      ((tateCohomologyFunctor n).mapIso ((resFunctor S.subtype).mapIso
        (equivalenceModuleMonoidAlgebra.unitIso.app A)))

/-- **Tensoring a resolution of length one.** Let `0 → P₁ → P₀ → A → 0` be a short exact sequence of
representations whose first two terms are projective `k[G]`-modules, and suppose that
`M ⊗ P₁ → M ⊗ P₀` is injective. Then for every finite subgroup `S` of `G` the Tate cohomology of
`S` with coefficients in `M ⊗ A` vanishes in every degree. -/
theorem isZero_res_tensor_of_shortExact (M : Rep k G) {T : ShortComplex (Rep k G)}
    (hT : T.ShortExact) [Module.Projective (MonoidAlgebra k G) T.X₁.ρ.asModule]
    [Module.Projective (MonoidAlgebra k G) T.X₂.ρ.asModule]
    (hf : Function.Injective (T.f.hom.toLinearMap.lTensor M.V)) (S : Subgroup G) [Fintype S]
    (n : ℤ) : IsZero (tateCohomology (res S.subtype (M ⊗ T.X₃)) n) :=
  have := hT.epi_g
  TauCeti.TateCohomology.isZero_X₃_of_isZero_X₂_of_isZero_X₁
    ((shortExact_map_tensorLeft_of_injective hT.exact M hf).map_of_exact (resFunctor S.subtype))
    n (n + 1) rfl (isZero_res_tensor_of_projective M _ S n)
    (isZero_res_tensor_of_projective M _ S (n + 1))

end Rep
