/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.Finrank
public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.PGroupInvariants
public import TauCeti.RepresentationTheory.OfModule
public import TauCeti.RepresentationTheory.AsModule

/-!
# Grothendieck classes of representations with `p`-power-order image

Over a field of characteristic `p`, a representation of a finite group in which every element
acts with `p`-power order has only trivial composition factors. Its class in the exact
Grothendieck group is therefore its dimension times the class of the trivial line. The group
itself need not be a `p`-group, and the representation need not split into trivial lines.

The module statement expresses the power-order hypothesis using the group-algebra basis
vectors, so it passes directly to submodules and quotients. The representation statement
`TauCeti.exactK0_asModule_eq_finrank_nsmul_of_forall_pow_eq_one` uses powers of the representing
endomorphisms instead. These results apply, for example, to permutation representations of
quotients of `p`-power order and allow their induced classes to be computed additively.

The simple-module argument uses the invariant-vector theorem in
`TauCeti/RepresentationTheory/PGroupInvariants.lean`; finite-length induction supplies the
exact-sequence relations for arbitrary modules.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part III, §14.
-/

public section

namespace TauCeti

open CategoryTheory.Limits
open scoped MonoidAlgebra ModuleCat

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G]
  (p : ℕ) [Fact p.Prime] [CharP k p]

/-- A simple group-algebra module on which every group element acts with `p`-power order
in characteristic `p` is isomorphic to the trivial line. -/
theorem nonempty_linearEquiv_trivial_of_forall_pow_eq_one
    (M : Type*) [AddCommGroup M] [Module k M] [Module k[G] M] [IsScalarTower k k[G] M]
    [IsSimpleModule k[G] M]
    (hM : ∀ g : G, ∃ n : ℕ, ∀ x : M, MonoidAlgebra.single (g ^ p ^ n) (1 : k) • x = x) :
    Nonempty (M ≃ₗ[k[G]] (Representation.trivial k G k).asModule) := by
  let ρ := Representation.ofModule' (k := k) (G := G) M
  have hρ : ρ.IsIrreducible := Representation.isIrreducible_ofModule'_iff M |>.mpr inferInstance
  have hpow : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1 := by
    intro g
    obtain ⟨n, hn⟩ := hM g
    refine ⟨n, ?_⟩
    rw [← map_pow]
    ext x
    exact hn x
  have htriv := hρ.eq_trivial_of_forall_pow_eq_one p hpow
  have hdim := hρ.finrank_eq_one_of_forall_pow_eq_one p hpow
  have := hρ.finiteDimensional
  let e := LinearEquiv.ofFinrankEq M k (hdim.trans (Module.finrank_self k).symm)
  have he : ρ.Equiv (Representation.trivial k G k) := Representation.Equiv.mk e (by
    intro g
    rw [htriv]
    ext x
    simp)
  exact ⟨(Representation.ofModule'AsModuleEquiv M).symm.trans
    (Representation.asModuleLinearEquivOfEquiv he)⟩

variable {G : Type u} [Group G] [Finite G]

/-- A finitely generated group-algebra module with `p`-power-order image in characteristic `p`
has Grothendieck class equal to its dimension times the trivial class. The exponent may depend
on the group element; no semisimplicity is assumed. -/
theorem exactK0_of_eq_finrank_smul_of_forall_pow_eq_one (M : FGModuleCat.{u} k[G])
    (hM : ∀ g : G, ∃ n : ℕ, ∀ x : M, MonoidAlgebra.single (g ^ p ^ n) (1 : k) • x = x) :
    (ExactK0.of M : ExactK0 (finiteModulesExactStructure k[G])) =
      (Module.finrank k M.obj : ℤ) •
        ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  let : IsArtinianRing k[G] := IsArtinianRing.of_finite k k[G]
  let t : ExactK0 (finiteModulesExactStructure k[G]) :=
    ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule)
  have ht : finrankK0 k k[G] t = 1 := by
    rw [finrankK0_of]
    exact_mod_cast (Representation.finrank_moduleCat_asModule
      (Representation.trivial k G k)).trans (Module.finrank_self k)
  have hfinite : IsFiniteLength k[G] M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  -- Induct through simple quotients, carrying the power-order condition with each module.
  suffices h : ∀ (X : Type u) [AddCommGroup X] [Module k[G] X], IsFiniteLength k[G] X →
      ∀ hX : Module.Finite k[G] X,
        (∀ g : G, ∃ n : ℕ, ∀ x : X, MonoidAlgebra.single (g ^ p ^ n) (1 : k) • x = x) →
        (ExactK0.of (@FGModuleCat.of k[G] _ X _ _ hX) :
          ExactK0 (finiteModulesExactStructure k[G])) =
        finrankK0 k k[G] (ExactK0.of (@FGModuleCat.of k[G] _ X _ _ hX)) • t by
    simpa only [finrankK0_of] using h M hfinite inferInstance hM
  intro X _ _ hX
  induction hX with
  | @of_subsingleton X _ _ _ =>
    intro hfg _
    let := hfg
    have hz : IsZero (FGModuleCat.of k[G] X) := IsZero.of_full_of_faithful_of_isZero
      (ModuleCat.isFG k[G]).ι _ (ModuleCat.isZero_of_subsingleton (ModuleCat.of k[G] X))
    simp [ExactK0.of_eq_zero_of_isZero hz]
  | @of_simple_quotient X _ _ N _ hN ih =>
    intro hfg hpow
    let := hfg
    have : IsNoetherian k[G] N := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
    have : Module.Finite k[G] N := inferInstance
    -- The same exponent works on the submodule and its quotient.
    have hNpow : ∀ g : G, ∃ n : ℕ,
        ∀ x : N, MonoidAlgebra.single (g ^ p ^ n) (1 : k) • x = x := by
      intro g
      obtain ⟨n, hn⟩ := hpow g
      exact ⟨n, fun x ↦ Subtype.ext (hn x)⟩
    have hQpow : ∀ g : G, ∃ n : ℕ,
        ∀ x : X ⧸ N, MonoidAlgebra.single (g ^ p ^ n) (1 : k) • x = x := by
      intro g
      obtain ⟨n, hn⟩ := hpow g
      refine ⟨n, fun x ↦ ?_⟩
      obtain ⟨y, rfl⟩ := N.mkQ_surjective x
      exact (N.mkQ.map_smul _ y).symm.trans (congrArg N.mkQ (hn y))
    let := Module.restrictScalars k k[G] (X ⧸ N)
    let := IsScalarTower.restrictScalars k k[G] (X ⧸ N)
    obtain ⟨e⟩ := nonempty_linearEquiv_trivial_of_forall_pow_eq_one p
      (ModuleCat.of k[G] (X ⧸ N)) hQpow
    have hQ : (ExactK0.of (FGModuleCat.of k[G] (X ⧸ N)) :
        ExactK0 (finiteModulesExactStructure k[G])) = t := ExactK0.of_congr e.toFGModuleCatIso
    -- The quotient is a trivial line. Add its class to the induction hypothesis.
    have hrel : (ExactK0.of (FGModuleCat.of k[G] X) :
        ExactK0 (finiteModulesExactStructure k[G])) =
        ExactK0.of (FGModuleCat.of k[G] N) + t := by
      rw [exactK0_of_eq_submodule_add_quotient k[G] N, hQ]
    calc
      ExactK0.of (FGModuleCat.of k[G] X) = ExactK0.of (FGModuleCat.of k[G] N) + t := hrel
      _ = (finrankK0 k k[G] (ExactK0.of (FGModuleCat.of k[G] N)) + 1) • t := by
        rw [ih inferInstance hNpow]
        simp [add_zsmul, ht]
      _ = finrankK0 k k[G] (ExactK0.of (FGModuleCat.of k[G] X)) • t := by
        rw [hrel]
        simp [ht]

/-- The class of a finite-dimensional representation with `p`-power-order image in
characteristic `p` is its dimension times the class of the trivial line, including when its
trivial composition factors do not split. -/
theorem exactK0_asModule_eq_finrank_nsmul_of_forall_pow_eq_one
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) (hρ : ∀ g : G, ∃ n : ℕ, ρ g ^ p ^ n = 1) :
    letI : Module.Finite k[G] ρ.asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule
    (ExactK0.of (FGModuleCat.of k[G] ρ.asModule) :
      ExactK0 (finiteModulesExactStructure k[G])) =
      Module.finrank k V •
        ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  let : Module.Finite k[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite k k[G] ρ.asModule
  have hpow : ∀ g : G, ∃ n : ℕ,
      ∀ x : ρ.asModule, MonoidAlgebra.single (g ^ p ^ n) (1 : k) • x = x := by
    intro g
    obtain ⟨n, hn⟩ := hρ g
    refine ⟨n, fun x ↦ ρ.asModuleEquiv.injective ?_⟩
    simp only [Representation.single_smul, one_smul]
    rw [map_pow, hn]
    rfl
  have h := exactK0_of_eq_finrank_smul_of_forall_pow_eq_one p
    (FGModuleCat.of k[G] ρ.asModule) hpow
  have hdim := Representation.finrank_moduleCat_asModule ρ
  simpa only [hdim, natCast_zsmul] using h

end TauCeti
