/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.MuNRep
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality

/-!
# The Tate dual and its evaluation pairing

For a `ZMod n`-representation `A` of the absolute Galois group of a field `F`, its Tate dual is

```text
A' = Hom(A, μₙ),
```

with the conjugation action.  This file packages Tau Ceti's generic `InternalHom` as a Galois
coefficient object and records the evaluation pairing `A' × A → μₙ`.  It also defines the
cohomological pairing in complementary degrees whose perfectness is local Tate duality.

The construction uses the internal hom and evaluation pairing from
`TauCeti.Topology.Algebra.GroupAction.InternalHom`, rather than introducing a parallel dual.  The
contravariant map on duals is precomposition, and evaluation is natural with respect to it.

The definitions follow the coefficient conventions of Neukirch--Schmidt--Wingberg,
*Cohomology of Number Fields*, 2nd ed., (7.2.6), and Serre, *Galois Cohomology*, Chapter II,
§5.2.

## Main definitions

* `TauCeti.ClassFieldTheory.tateDual`: the conjugation module `Hom(A, μₙ)`.
* `TauCeti.ClassFieldTheory.tateEvaluationPairing`: the named evaluation pairing.
* `TauCeti.ClassFieldTheory.tateDualMap`: precomposition on Tate duals.
* `TauCeti.ClassFieldTheory.tateDualityPairing`: evaluation cup product in complementary degrees,
  followed by a chosen local invariant on `H²(F, μₙ)`.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open CategoryTheory

universe u

attribute [local instance] TopRep.distribMulAction

variable {n : ℕ} {F : Type u} [Field F]

/-! ### The coefficient object -/

/-- The internal hom `Hom(A, μₙ)` is killed by `n`. -/
theorem nsmul_internalHom_eq_zero (A : GalRep n F)
    (φ : InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V) : n • φ = 0 := by
  exact InternalHom.nsmul_eq_zero (fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]) φ

/-- The `ZMod n`-module structure on `Hom(A, μₙ)`. -/
@[instance_reducible]
noncomputable def internalHomModule (A : GalRep n F) :
    Module (ZMod n) (InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V) :=
  AddCommGroup.zmodModule (nsmul_internalHom_eq_zero A)

attribute [local instance] internalHomModule

/-- The conjugation action on `Hom(A, μₙ)` commutes with its `ZMod n`-scalar action. -/
theorem internalHom_smulCommClass (A : GalRep n F) :
    SMulCommClass (Field.absoluteGaloisGroup F) (ZMod n)
      (InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V) :=
  ⟨fun g c φ => ZMod.map_smul
    (DistribSMul.toAddMonoidHom
      (InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V) g) c φ⟩

/-- Scalar multiplication on the discrete internal hom is continuous. -/
theorem internalHom_continuousSMul (A : GalRep n F) :
    ContinuousSMul (ZMod n)
      (InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V) :=
  ⟨continuous_of_discreteTopology⟩

attribute [local instance] internalHom_smulCommClass internalHom_continuousSMul

/-- **The Tate dual** `A' = Hom(A, μₙ)`, with the conjugation action. -/
@[expose] def tateDual (A : GalRep n F) : GalRep n F :=
  ofDiscreteModule (ZMod n) (Field.absoluteGaloisGroup F)
    (InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V)

/-- The Tate dual carries the discrete topology. -/
instance instDiscreteTopologyTateDual (A : GalRep n F) : DiscreteTopology (tateDual A).V :=
  inferInstanceAs (DiscreteTopology
    (InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V))

/-- The carrier of the Tate dual is the group of additive maps `A →+ μₙ`. -/
def tateDualEquiv (A : GalRep n F) : (tateDual A).V ≃+ (A.V →+ (muNRep n F).V) where
  toFun φ := InternalHom.evalPairing (Field.absoluteGaloisGroup F) φ
  invFun f := InternalHom.of (Field.absoluteGaloisGroup F) f
  left_inv φ := by
    change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
    exact (congrArg (InternalHom.of (Field.absoluteGaloisGroup F))
      (InternalHom.evalPairing_apply φ)).trans (InternalHom.of_toAddMonoidHom φ)
  right_inv f := by
    change InternalHom.evalPairing (Field.absoluteGaloisGroup F)
      (InternalHom.of (Field.absoluteGaloisGroup F) f) = f
    rw [InternalHom.evalPairing_apply]
  map_add' := map_add (InternalHom.evalPairing (Field.absoluteGaloisGroup F))

/-- The carrier equivalence of the Tate dual forgets only the conjugation action. -/
theorem tateDualEquiv_apply (A : GalRep n F) (φ : (tateDual A).V) :
    tateDualEquiv A φ = φ.toAddMonoidHom := by
  change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
  unfold tateDualEquiv
  exact InternalHom.evalPairing_apply φ

/-- The action on the Tate dual is conjugation: `(g · φ)(a) = g · φ(g⁻¹ · a)`. -/
@[simp]
theorem tateDualEquiv_ρ_apply (A : GalRep n F) (g : Field.absoluteGaloisGroup F)
    (φ : (tateDual A).V) (a : A.V) :
    tateDualEquiv A ((tateDual A).ρ g φ) a =
      (muNRep n F).ρ g (tateDualEquiv A φ (A.ρ g⁻¹ a)) := by
  rw [tateDualEquiv_apply, tateDualEquiv_apply]
  change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
  change (g • φ).toAddMonoidHom a = g • φ.toAddMonoidHom (g⁻¹ • a)
  rw [InternalHom.toAddMonoidHom_smul, TauCeti.homAction_apply]

/-- `Hom(A, μₙ)` is finite when `A` is finite and `n` is nonzero. -/
instance instFiniteTateDual [NeZero n] (A : GalRep n F) [Finite A.V] : Finite (tateDual A).V :=
  letI : Finite (muNRep n F).V :=
    Finite.of_equiv (KummerCoeff F n) (kummerCoeffEquivMuNRep n F).toEquiv
  inferInstanceAs (Finite (InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V))

/-- The Tate dual of a finite smooth discrete module is smooth discrete. -/
theorem isSmoothDiscrete_tateDual (A : GalRep n F) [DiscreteTopology A.V] [Finite A.V]
    (hA : IsSmoothDiscrete (ZMod n) A) : IsSmoothDiscrete (ZMod n) (tateDual A) := by
  let _ := hA.continuousSMul
  exact ofDiscreteModule_isSmoothDiscrete (ZMod n) (Field.absoluteGaloisGroup F) _

/-- Smoothness of the Tate dual, available to local-duality consumers by instance search. -/
instance instFactIsSmoothDiscreteTateDual (A : GalRep n F) [DiscreteTopology A.V] [Finite A.V]
    [hA : Fact (IsSmoothDiscrete (ZMod n) A)] : Fact (IsSmoothDiscrete (ZMod n) (tateDual A)) :=
  ⟨isSmoothDiscrete_tateDual A hA.out⟩

/-- An element of the Tate dual is fixed by `g` exactly when it intertwines the action of `g`. -/
theorem tateDual_ρ_eq_self_iff (A : GalRep n F) (g : Field.absoluteGaloisGroup F)
    (φ : (tateDual A).V) :
    (tateDual A).ρ g φ = φ ↔
      ∀ a : A.V, tateDualEquiv A φ (A.ρ g a) =
        (muNRep n F).ρ g (tateDualEquiv A φ a) := by
  rw [tateDualEquiv_apply]
  change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
  exact InternalHom.smul_eq_self_iff

/-! ### Evaluation and contravariance -/

/-- **The evaluation pairing** `Hom(A, μₙ) × A → μₙ`, `( φ, a ) ↦ φ(a)`. -/
def tateEvaluationPairing (A : GalRep n F) [DiscreteTopology A.V] :
    TauCeti.TopPairing (tateDual A) A (muNRep n F) where
  bil := AddMonoidHom.toZModLinearMap n
    { toFun := fun φ => AddMonoidHom.toZModLinearMap n
        φ.toAddMonoidHom
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  cont := continuous_of_discreteTopology
  equivariant g φ a := by
    change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
    change (g • φ).toAddMonoidHom (g • a) = g • φ.toAddMonoidHom a
    rw [InternalHom.toAddMonoidHom_smul, TauCeti.homAction_apply_smul]

/-- The named Tate evaluation pairing is ordinary evaluation. -/
@[simp]
theorem tateEvaluationPairing_bil (A : GalRep n F) [DiscreteTopology A.V]
    (φ : (tateDual A).V) (a : A.V) :
    (tateEvaluationPairing A).bil φ a = tateDualEquiv A φ a := by
  rw [tateDualEquiv_apply]
  change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
  rfl

/-- A morphism of Galois representations, regarded as an equivariant additive homomorphism. -/
private def tateDualSourceMap {A B : GalRep n F} (f : A ⟶ B) :
    A.V →+[Field.absoluteGaloisGroup F] B.V where
  toFun := f.hom
  map_zero' := map_zero f.hom
  map_add' := map_add f.hom
  map_smul' := fun g a => TopRep.hom_comm_apply f g a

/-- **The Tate dual is contravariant**: `f : A ⟶ B` induces `f* : B' ⟶ A'` by
precomposition. -/
def tateDualMap {A B : GalRep n F} (f : A ⟶ B) : tateDual B ⟶ tateDual A :=
  ofDiscreteModuleMap
    (AddMonoidHom.toZModLinearMap n
      (InternalHom.precomp (Field.absoluteGaloisGroup F) (tateDualSourceMap f)).toAddMonoidHom)
    fun g ψ => map_smul
      (InternalHom.precomp (Field.absoluteGaloisGroup F) (tateDualSourceMap f)) g ψ

/-- `tateDualMap f` acts by precomposition with `f`. -/
@[simp]
theorem tateDualEquiv_tateDualMap_apply {A B : GalRep n F} (f : A ⟶ B)
    (ψ : (tateDual B).V) (a : A.V) :
    tateDualEquiv A ((tateDualMap f).hom ψ) a = tateDualEquiv B ψ (f.hom a) :=
  by
    rw [tateDualEquiv_apply, tateDualEquiv_apply]
    change InternalHom (Field.absoluteGaloisGroup F) B.V (muNRep n F).V at ψ
    have hmap : (tateDualMap f).hom ψ =
        InternalHom.precomp (Field.absoluteGaloisGroup F) (tateDualSourceMap f) ψ := by
      apply ofDiscreteModuleMap_hom_apply
    rw [hmap]
    exact congrArg (fun q : A.V →+ (muNRep n F).V => q a)
      (InternalHom.toAddMonoidHom_precomp _ ψ)

/-- Evaluation is natural in the coefficient module: `⟨f* ψ, a⟩ = ⟨ψ, f a⟩`. -/
theorem tateEvaluationPairing_tateDualMap {A B : GalRep n F} [DiscreteTopology A.V]
    [DiscreteTopology B.V] (f : A ⟶ B) (ψ : (tateDual B).V) (a : A.V) :
    (tateEvaluationPairing A).bil ((tateDualMap f).hom ψ) a =
      (tateEvaluationPairing B).bil ψ (f.hom a) :=
  by
    simpa only [tateEvaluationPairing_bil] using
      (tateDualEquiv_tateDualMap_apply f ψ a)

/-! ### The cohomological pairing -/

/-- **The local Tate-duality pairing** in complementary degrees, formed from the named evaluation
pairing and an identification of `H²(F, μₙ)` with `ZMod n`. -/
def tateDualityPairing (A : GalRep n F) [DiscreteTopology A.V]
    (tr : _root_.continuousCohomology.{0, u, u} 2 (muNRep n F) ≃+ ZMod n)
    (i j : ℕ) (hij : i + j = 2)
    (x : _root_.continuousCohomology.{0, u, u} i (tateDual A))
    (y : _root_.continuousCohomology.{0, u, u} j A) : ZMod n :=
  tr (hij ▸ TopPairing.cup.{0, u, u} (tateEvaluationPairing A) i j x y)

/-- **Naturality of the local Tate-duality pairing**:
`⟨f* x, y⟩ = ⟨x, f* y⟩`. -/
theorem tateDualityPairing_tateDualMap {A B : GalRep n F}
    [DiscreteTopology A.V] [DiscreteTopology B.V] (f : A ⟶ B)
    (tr : _root_.continuousCohomology.{0, u, u} 2 (muNRep n F) ≃+ ZMod n)
    (i j : ℕ) (hij : i + j = 2)
    (x : _root_.continuousCohomology.{0, u, u} i (tateDual B))
    (y : _root_.continuousCohomology.{0, u, u} j A) :
    tateDualityPairing A tr i j hij
        ((ContinuousCohomology.coeffMap (tateDualMap f) i).hom x) y =
      tateDualityPairing B tr i j hij x
        ((ContinuousCohomology.coeffMap f j).hom y) := by
  have hid : ∀ (X : GalRep n F) (m : ℕ)
      (z : _root_.continuousCohomology.{0, u, u} m X),
      (ContinuousCohomology.coeffMap (𝟙 X) m).hom z = z := fun X m z => by
    rw [ContinuousCohomology.coeffMap_id]
    rfl
  let Q : TauCeti.TopPairing (tateDual B) A (muNRep n F) :=
    { bil := (tateEvaluationPairing B).bil.compl₂ f.hom.toContinuousLinearMap.toLinearMap
      cont := continuous_of_discreteTopology
      equivariant := fun g ψ a => by
        change (tateEvaluationPairing B).bil ((tateDual B).ρ g ψ) (f.hom (A.ρ g a)) = _
        rw [TopRep.hom_comm_apply]
        exact (tateEvaluationPairing B).equivariant g ψ (f.hom a) }
  have h₁ := (hid _ (i + j) _).symm.trans (Q.cup_coeffMap (tateEvaluationPairing A)
    (tateDualMap f) (𝟙 _) (𝟙 _)
    (fun ψ a => (tateEvaluationPairing_tateDualMap f ψ a).symm) i j x y)
  have h₂ := (hid _ (i + j) _).symm.trans (Q.cup_coeffMap (tateEvaluationPairing B)
    (𝟙 _) f (𝟙 _) (fun _ _ => rfl) i j x y)
  simp only [hid] at h₁ h₂
  simp only [tateDualityPairing]
  rw [← h₁, ← h₂]

end TauCeti.ClassFieldTheory
