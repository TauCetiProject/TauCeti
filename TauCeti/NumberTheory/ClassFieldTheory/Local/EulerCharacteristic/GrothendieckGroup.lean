/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Ring.Units
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteQuotient
public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Additivity
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Universal

/-!
# The local Euler characteristic on the Grothendieck group of a finite Galois quotient

Let `V` be an open normal subgroup of the absolute Galois group `G_F` of a nonarchimedean local
field `F`, and let `n` be invertible in `F`. A finite-dimensional `ZMod n`-representation of the
finite group `G_F ⧸ V` is a finite smooth discrete Galois representation through
`fdGalRepOfQuotient`, the restriction of `galRepOfQuotient` to finite-dimensional
representations. By the multiplicativity of the local Euler characteristic `χ_F` and of the
normalized absolute value `φ_F` of the order in short exact sequences, both invariants of these
inflated representations descend to homomorphisms

```text
G₀((ZMod n)[G_F ⧸ V]) → Additive ℚ^×_{>0}
```

through the universal property `TauCeti.liftFDRepK0`. As every finite smooth discrete Galois
representation is inflated from some finite quotient (`exists_galRepOfQuotient_iso`), Tate's
local Euler characteristic formula `χ_F = φ_F` holds exactly when these two homomorphisms agree
for every `V`. Since `ℚ^×_{>0}` is torsion-free (`Units.instIsMulTorsionFreePosSubgroup`), that
agreement may be checked on a positive multiple of each class, such as the one the modular Artin
theorem writes as a sum of classes induced from cyclic subgroups.

## Main definitions

* `TauCeti.ClassFieldTheory.fdGalRepOfQuotient`: inflation of finite-dimensional representations
  of `G_F ⧸ V` to Galois representations.
* `TauCeti.ClassFieldTheory.localEulerCharacteristicK0`: the descended Euler characteristic.
* `TauCeti.ClassFieldTheory.localCardNormK0`: the descended normalized absolute value of the order.

## Main results

* `TauCeti.ClassFieldTheory.localEulerCharacteristicK0_of`,
  `TauCeti.ClassFieldTheory.localCardNormK0_of`: the values on the class of a representation.
* `TauCeti.ClassFieldTheory.localEulerCharacteristicK0_eq_localCardNormK0_iff`: the two
  homomorphisms for `V` agree exactly when `χ_F = φ_F` on every finite smooth discrete
  representation on which `V` acts trivially.
* `TauCeti.ClassFieldTheory.forall_localEulerCharacteristic_eq_localCardNorm_iff`: `χ_F = φ_F` on
  every finite smooth discrete representation exactly when the two homomorphisms agree for every
  `V`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, §VII.3,
  proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, I, proof of Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory
open scoped MonoidAlgebra

variable (n : ℕ) (F : Type) [Field F] (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F))

variable {n F V} [NeZero n] in
/-- A short exact sequence of finite-dimensional representations of a finite Galois quotient
inflates to an injection, an exact pair and a surjection of Galois representations. -/
private theorem injective_exact_surjective_fdGalRepOfQuotient
    {S : ShortComplex (FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))}
    (hS : S.ShortExact) :
    Function.Injective ((fdGalRepOfQuotient n F V).map S.f).hom ∧
      Function.Exact ((fdGalRepOfQuotient n F V).map S.f).hom
        ((fdGalRepOfQuotient n F V).map S.g).hom ∧
      Function.Surjective ((fdGalRepOfQuotient n F V).map S.g).hom := by
  apply (fdGalRepOfQuotient_injective_exact_surjective_iff n F V S.f S.g).2
  have h := hS.map_of_exact (forget₂ (FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup))
    (Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) ⋙
      forget₂ (Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) (ModuleCat (ZMod n)))
  exact ⟨h.moduleCat_injective_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h.exact,
    h.moduleCat_surjective_g⟩

variable {n F} [NeZero n]

section EulerCharacteristic

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **The local Euler characteristic on `G₀` of a finite Galois quotient.** For `n` invertible in
`F`, the local Euler characteristic of inflated representations descends to the Grothendieck group
of finite `(ZMod n)[G_F ⧸ V]`-modules, by its multiplicativity in short exact sequences
(`localEulerCharacteristic_mul_of_exact`). -/
def localEulerCharacteristicK0 (hn : IsUnit (n : F)) :
    ExactK0 (finiteModulesExactStructure (ZMod n)[Field.absoluteGaloisGroup F ⧸ V.toSubgroup]) →+
      Additive (Units.posSubgroup ℚ) :=
  liftFDRepK0
    (fun A ↦ .ofMul (localEulerCharacteristic hn.ne_zero ((fdGalRepOfQuotient n F V).obj A)))
    fun _ hS ↦ by
      obtain ⟨hf, hfg, hg⟩ := injective_exact_surjective_fdGalRepOfQuotient hS
      exact congrArg Additive.ofMul (localEulerCharacteristic_mul_of_exact hn _ _ hf hfg hg)

/-- The descended Euler characteristic takes the value `χ_F` of the inflated representation on the
class of a finite-dimensional representation. -/
@[simp]
theorem localEulerCharacteristicK0_of (hn : IsUnit (n : F))
    (A : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    letI : Module.Finite (ZMod n)[Field.absoluteGaloisGroup F ⧸ V.toSubgroup]
        (Representation.asModule A.ρ) :=
      Module.Finite.of_restrictScalars_finite (ZMod n) _ _
    localEulerCharacteristicK0 V hn
        (ExactK0.of (FGModuleCat.of _ (Representation.asModule A.ρ))) =
      .ofMul (localEulerCharacteristic hn.ne_zero ((fdGalRepOfQuotient n F V).obj A)) :=
  liftFDRepK0_of _ _ A

end EulerCharacteristic

section CardNorm

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (p : ℕ) [Fact p.Prime] [FinitePadicExtension F p]

variable (n) in
/-- **The normalized absolute value of the order on `G₀` of a finite Galois quotient.** The
invariant `φ_F` of inflated representations descends to the Grothendieck group of finite
`(ZMod n)[G_F ⧸ V]`-modules, by its multiplicativity in short exact sequences
(`localCardNorm_mul_of_exact`). -/
def localCardNormK0 :
    ExactK0 (finiteModulesExactStructure (ZMod n)[Field.absoluteGaloisGroup F ⧸ V.toSubgroup]) →+
      Additive (Units.posSubgroup ℚ) :=
  liftFDRepK0 (fun A ↦ .ofMul (localCardNorm p ((fdGalRepOfQuotient n F V).obj A)))
    fun _ hS ↦ by
      obtain ⟨hf, hfg, hg⟩ := injective_exact_surjective_fdGalRepOfQuotient hS
      exact congrArg Additive.ofMul (localCardNorm_mul_of_exact p _ _ hf hfg hg)

/-- The descended normalized absolute value takes the value `φ_F` of the inflated representation
on the class of a finite-dimensional representation. -/
@[simp]
theorem localCardNormK0_of (A : FDRep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) :
    letI : Module.Finite (ZMod n)[Field.absoluteGaloisGroup F ⧸ V.toSubgroup]
        (Representation.asModule A.ρ) :=
      Module.Finite.of_restrictScalars_finite (ZMod n) _ _
    localCardNormK0 n V p (ExactK0.of (FGModuleCat.of _ (Representation.asModule A.ρ))) =
      .ofMul (localCardNorm p ((fdGalRepOfQuotient n F V).obj A)) :=
  liftFDRepK0_of _ _ A

end CardNorm

section Comparison

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (p : ℕ) [Fact p.Prime] [FinitePadicExtension F p]

/-- If the two descended homomorphisms for `V` agree, then `χ_F = φ_F` on every Galois
representation isomorphic to the inflation of a finite representation of `G_F ⧸ V`. -/
private theorem localEulerCharacteristic_eq_localCardNorm_of_iso (hn : IsUnit (n : F))
    (h : localEulerCharacteristicK0 V hn = localCardNormK0 n V p)
    (A : Rep (ZMod n) (Field.absoluteGaloisGroup F ⧸ V.toSubgroup)) [Finite A.V]
    {X : GalRep n F} [Finite X.V] [Fact (IsSmoothDiscrete (ZMod n) X)]
    (e : (galRepOfQuotient n F V).obj A ≅ X) :
    localEulerCharacteristic hn.ne_zero X = localCardNorm p X := by
  have : Module.Finite (ZMod n) A.V := Module.Finite.of_finite
  have : Module.Finite (ZMod n)[Field.absoluteGaloisGroup F ⧸ V.toSubgroup]
      (Representation.asModule (FDRep.of A.ρ).ρ) :=
    Module.Finite.of_restrictScalars_finite (ZMod n) _ _
  have hA := DFunLike.congr_fun h
    (ExactK0.of (FGModuleCat.of _ (Representation.asModule (FDRep.of A.ρ).ρ)))
  rw [localEulerCharacteristicK0_of, localCardNormK0_of] at hA
  let e' := eqToIso (fdGalRepOfQuotient_obj_of n F V A) ≪≫ e
  rw [← localEulerCharacteristic_congr hn.ne_zero e', ← localCardNorm_congr p e']
  exact Additive.ofMul.injective hA

/-- **The Euler characteristic formula for `V` on `G₀`.** The descended Euler characteristic and
the descended normalized absolute value of the order agree on the Grothendieck group of
`(ZMod n)[G_F ⧸ V]` exactly when `χ_F(X) = φ_F(X)` for every finite smooth discrete Galois
representation `X` on which `V` acts trivially. -/
theorem localEulerCharacteristicK0_eq_localCardNormK0_iff (hn : IsUnit (n : F)) :
    localEulerCharacteristicK0 V hn = localCardNormK0 n V p ↔
      ∀ (X : GalRep n F) [Finite X.V] [DiscreteTopology X.V]
        [Fact (IsSmoothDiscrete (ZMod n) X)], (∀ g ∈ V, ∀ x : X.V, X.ρ g x = x) →
          localEulerCharacteristic hn.ne_zero X = localCardNorm p X := by
  refine ⟨fun h X _ _ _ hX ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨A, ⟨e⟩⟩ := exists_galRepOfQuotient_iso_of_trivial n F V X hX
    have : Finite A.V := by
      have hfin : Finite ((galRepOfQuotient n F V).obj A).V :=
        Finite.of_equiv X.V ((forget (GalRep n F)).mapIso e).toEquiv.symm
      rwa [galRepOfQuotient_obj_V] at hfin
    exact localEulerCharacteristic_eq_localCardNorm_of_iso V p hn h A e
  · refine (liftFDRepK0_unique _ _ _ fun A ↦ ?_).symm
    rw [localCardNormK0_of, h _ fun g hg x ↦ fdGalRepOfQuotient_ρ_eq_self n F V A hg x]

/-- **The Euler characteristic formula and `G₀`.** Tate's local Euler characteristic formula
`χ_F(X) = φ_F(X)` holds for every finite smooth discrete Galois representation `X` exactly when, for
every open normal subgroup `V` of `G_F`, the descended Euler characteristic and the descended
normalized absolute value of the order agree on the Grothendieck group of `(ZMod n)[G_F ⧸ V]`. -/
theorem forall_localEulerCharacteristic_eq_localCardNorm_iff (hn : IsUnit (n : F)) :
    (∀ (X : GalRep n F) [Finite X.V] [DiscreteTopology X.V]
        [Fact (IsSmoothDiscrete (ZMod n) X)],
          localEulerCharacteristic hn.ne_zero X = localCardNorm p X) ↔
      ∀ V : OpenNormalSubgroup (Field.absoluteGaloisGroup F),
        localEulerCharacteristicK0 V hn = localCardNormK0 n V p := by
  refine ⟨fun h V ↦ (localEulerCharacteristicK0_eq_localCardNormK0_iff V p hn).2
    fun X _ _ _ _ ↦ h X, fun h X _ _ _ ↦ ?_⟩
  obtain ⟨V, A, _, ⟨e⟩⟩ := exists_galRepOfQuotient_iso n F X
  exact localEulerCharacteristic_eq_localCardNorm_of_iso V p hn (h V) A e

end Comparison

end TauCeti.ClassFieldTheory
