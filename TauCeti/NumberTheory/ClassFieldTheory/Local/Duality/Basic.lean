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
contravariant map on duals is precomposition, and evaluation is natural with respect to it.  When
`n` is invertible in `F`, `μₙ` is cyclic of order `n`, hence an injective `ZMod n`-module, and
the dual of a short exact sequence is short exact.

The definitions follow the coefficient conventions of Neukirch--Schmidt--Wingberg,
*Cohomology of Number Fields*, 2nd ed., (7.2.6), and Serre, *Galois Cohomology*, Chapter II,
§5.2.

## Main definitions

* `TauCeti.ClassFieldTheory.tateDual`: the conjugation module `Hom(A, μₙ)`.
* `TauCeti.ClassFieldTheory.tateEvaluationPairing`: the named evaluation pairing.
* `TauCeti.ClassFieldTheory.pairingToTateDual`: the morphism `A → B'` curried from a pairing
  `A × B → μₙ`.
* `TauCeti.ClassFieldTheory.tateDualMap`: precomposition on Tate duals.
* `TauCeti.ClassFieldTheory.tateDualityPairing`: evaluation cup product in complementary degrees,
  followed by a chosen local invariant on `H²(F, μₙ)`.

## Main results

* `TauCeti.ClassFieldTheory.tateDualMap_exact`: for `n` invertible in `F`, the Tate dual of a
  short exact sequence is short exact.
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
def tateDual (A : GalRep n F) : GalRep n F :=
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
  -- `(tateDual A).V` is `InternalHom _ A.V (muNRep n F).V` only by unfolding `ofDiscreteModule`
  -- (`ofDiscreteModule_V`), so `φ` is retyped before the `InternalHom` lemmas can match it.
  left_inv φ := by
    change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
    exact (congrArg (InternalHom.of (Field.absoluteGaloisGroup F))
      (InternalHom.evalPairing_apply φ)).trans (InternalHom.of_toAddMonoidHom φ)
  -- The composite is stated on the `InternalHom` carrier so that `evalPairing_apply` matches.
  right_inv f := by
    change InternalHom.evalPairing (Field.absoluteGaloisGroup F)
      (InternalHom.of (Field.absoluteGaloisGroup F) f) = f
    rw [InternalHom.evalPairing_apply]
  map_add' := map_add (InternalHom.evalPairing (Field.absoluteGaloisGroup F))

/-- The carrier equivalence of the Tate dual forgets only the conjugation action. This mentions the
`InternalHom` carrier hidden by `tateDual`, so it is private; consumers use the `tateDualEquiv`
API below. -/
private theorem tateDualEquiv_apply (A : GalRep n F) (φ : (tateDual A).V) :
    tateDualEquiv A φ = φ.toAddMonoidHom :=
  InternalHom.evalPairing_apply φ

/-- The action on the Tate dual is the conjugation action `homAction` on additive maps. -/
theorem tateDualEquiv_ρ (A : GalRep n F) (g : Field.absoluteGaloisGroup F)
    (φ : (tateDual A).V) :
    tateDualEquiv A ((tateDual A).ρ g φ) = TauCeti.homAction g (tateDualEquiv A φ) := by
  -- This is the one place where the operator of `ofDiscreteModule` is identified with the action
  -- on `InternalHom`; the other action lemmas are derived from it.
  rw [tateDualEquiv_apply, tateDualEquiv_apply]
  -- The operator of `g` on `ofDiscreteModule` is `g • ·` on its carrier `InternalHom`
  -- (`ofDiscreteModule_ρ_apply_apply`), which `rw` cannot see through the `tateDual` wrapper.
  change InternalHom (Field.absoluteGaloisGroup F) A.V (muNRep n F).V at φ
  exact InternalHom.toAddMonoidHom_smul g φ

/-- The action on the Tate dual is conjugation: `(g · φ)(a) = g · φ(g⁻¹ · a)`. -/
@[simp]
theorem tateDualEquiv_ρ_apply (A : GalRep n F) (g : Field.absoluteGaloisGroup F)
    (φ : (tateDual A).V) (a : A.V) :
    tateDualEquiv A ((tateDual A).ρ g φ) a =
      (muNRep n F).ρ g (tateDualEquiv A φ (A.ρ g⁻¹ a)) := by
  rw [tateDualEquiv_ρ, TauCeti.homAction_apply]
  -- `g • ·` on `A.V` and `μₙ` is `TopRep.distribMulAction`, i.e. the operator `ρ g`.
  rfl

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
  rw [← (tateDualEquiv A).injective.eq_iff, tateDualEquiv_ρ]
  exact TauCeti.homAction_eq_self_iff

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
  -- `bil φ a` is `φ.toAddMonoidHom a` by construction, so equivariance is the carrier statement
  -- `TauCeti.homAction_apply_smul` transported along `tateDualEquiv_ρ`.
  equivariant g φ a := by
    have h := congrArg (fun q : A.V →+ (muNRep n F).V => q (A.ρ g a)) (tateDualEquiv_ρ A g φ)
    simp only [tateDualEquiv_apply] at h
    exact h.trans (TauCeti.homAction_apply_smul g _ a)

/-- The named Tate evaluation pairing is ordinary evaluation. -/
@[simp]
theorem tateEvaluationPairing_bil (A : GalRep n F) [DiscreteTopology A.V]
    (φ : (tateDual A).V) (a : A.V) :
    (tateEvaluationPairing A).bil φ a = tateDualEquiv A φ a := by
  rw [tateDualEquiv_apply]
  -- `bil` is built from `φ.toAddMonoidHom` via `AddMonoidHom.toZModLinearMap`.
  rfl

/-- The additive currying `a ↦ (b ↦ P a b)` of a pairing into `μₙ`, landing in the Tate dual. -/
private def pairingToTateDualAddHom {A B : GalRep n F} (P : TopPairing A B (muNRep n F)) :
    A.V →+ (tateDual B).V :=
  (tateDualEquiv B).symm.toAddMonoidHom.comp
    (LinearMap.toAddMonoidHom'.comp P.bil.toAddMonoidHom)

/-- The additive currying evaluates to the pairing. -/
private theorem tateDualEquiv_pairingToTateDualAddHom_apply {A B : GalRep n F}
    (P : TopPairing A B (muNRep n F)) (a : A.V) (b : B.V) :
    tateDualEquiv B (pairingToTateDualAddHom P a) b = P.bil a b := by
  simp [pairingToTateDualAddHom]

/-- The currying of an equivariant pairing is equivariant:
`(g · P a)(b) = g · P a (g⁻¹ · b) = P (g · a) b`. -/
private theorem pairingToTateDualAddHom_ρ {A B : GalRep n F} (P : TopPairing A B (muNRep n F))
    (g : Field.absoluteGaloisGroup F) (a : A.V) :
    pairingToTateDualAddHom P (A.ρ g a) = (tateDual B).ρ g (pairingToTateDualAddHom P a) :=
  (tateDualEquiv B).injective <| AddMonoidHom.ext fun b => by
    simp only [tateDualEquiv_ρ_apply, tateDualEquiv_pairingToTateDualAddHom_apply,
      ← P.equivariant]
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

/-- **Currying a pairing into the Tate dual**: a coefficient pairing `A × B → μₙ` on a discrete
module `A` induces the morphism `A → B'`, `a ↦ (b ↦ P a b)`. -/
def pairingToTateDual {A B : GalRep n F} [DiscreteTopology A.V]
    (P : TopPairing A B (muNRep n F)) : A ⟶ tateDual B :=
  TopRep.ofHom
    { toContinuousLinearMap :=
        ⟨AddMonoidHom.toZModLinearMap n (pairingToTateDualAddHom P), continuous_of_discreteTopology⟩
      isIntertwining' g := ContinuousLinearMap.ext (pairingToTateDualAddHom_ρ P g) }

/-- The defining equation of `pairingToTateDual`: its underlying map is the additive currying. -/
private theorem pairingToTateDual_hom_apply {A B : GalRep n F} [DiscreteTopology A.V]
    (P : TopPairing A B (muNRep n F)) (a : A.V) :
    (pairingToTateDual P).hom a = pairingToTateDualAddHom P a :=
  rfl

/-- `pairingToTateDual P` sends `a` to the character `b ↦ P a b`. -/
@[simp]
theorem tateDualEquiv_pairingToTateDual_apply {A B : GalRep n F} [DiscreteTopology A.V]
    (P : TopPairing A B (muNRep n F)) (a : A.V) (b : B.V) :
    tateDualEquiv B ((pairingToTateDual P).hom a) b = P.bil a b := by
  rw [pairingToTateDual_hom_apply, tateDualEquiv_pairingToTateDualAddHom_apply]

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

/-- On the `InternalHom` carriers, `tateDualMap f` is `InternalHom.precomp` along `f`. This
mentions the carrier hidden by `tateDual`, so it is private; consumers use
`tateDualEquiv_tateDualMap_apply`. -/
private theorem coe_tateDualMap_hom {A B : GalRep n F} (f : A ⟶ B) :
    ⇑(tateDualMap f).hom =
      InternalHom.precomp (Field.absoluteGaloisGroup F) (tateDualSourceMap f) :=
  funext fun _ => by apply ofDiscreteModuleMap_hom_apply

/-- `tateDualMap f` acts by precomposition with `f`. -/
@[simp]
theorem tateDualEquiv_tateDualMap_apply {A B : GalRep n F} (f : A ⟶ B)
    (ψ : (tateDual B).V) (a : A.V) :
    tateDualEquiv A ((tateDualMap f).hom ψ) a = tateDualEquiv B ψ (f.hom a) := by
  rw [tateDualEquiv_apply, tateDualEquiv_apply, coe_tateDualMap_hom]
  exact congrArg (fun q : A.V →+ (muNRep n F).V => q a)
    (InternalHom.toAddMonoidHom_precomp _ ψ)

/-- Precomposition with the identity is the identity on the Tate dual. -/
@[simp]
theorem tateDualMap_id (A : GalRep n F) : tateDualMap (𝟙 A) = 𝟙 (tateDual A) :=
  TopRep.hom_ext <| DFunLike.ext _ _ fun ψ => (tateDualEquiv A).injective <|
    AddMonoidHom.ext fun a => tateDualEquiv_tateDualMap_apply (𝟙 A) ψ a

/-- The Tate dual reverses composition: `(f ≫ g)* = g* ≫ f*`. -/
@[simp]
theorem tateDualMap_comp {A B C : GalRep n F} (f : A ⟶ B) (g : B ⟶ C) :
    tateDualMap (f ≫ g) = tateDualMap g ≫ tateDualMap f :=
  TopRep.hom_ext <| DFunLike.ext _ _ fun ψ => (tateDualEquiv A).injective <|
    AddMonoidHom.ext fun a => by
      rw [TopRep.comp_apply, tateDualEquiv_tateDualMap_apply, tateDualEquiv_tateDualMap_apply,
        tateDualEquiv_tateDualMap_apply, TopRep.comp_apply]

/-! ### Exactness -/

/-- **The Tate dual turns surjections into injections**: if `g` is surjective, a character of `C`
vanishing on the image of `g` is zero. -/
theorem tateDualMap_injective_of_surjective {B C : GalRep n F} {g : B ⟶ C}
    (hg : Function.Surjective g.hom) : Function.Injective (tateDualMap g).hom := by
  rw [coe_tateDualMap_hom]
  exact InternalHom.precomp_injective hg

/-- **The Tate dual is exact in the middle**: if `f, g` are exact with `g` surjective, then
`g*, f*` are exact, a character of `B` killing the image of `f` factoring through `g`. -/
theorem exact_tateDualMap {A B C : GalRep n F} {f : A ⟶ B} {g : B ⟶ C}
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    Function.Exact (tateDualMap g).hom (tateDualMap f).hom := by
  rw [coe_tateDualMap_hom, coe_tateDualMap_hom]
  exact InternalHom.exact_precomp (tateDualSourceMap f) (tateDualSourceMap g) hg hfg

/-- **The Tate dual turns injections into surjections** when `n` is invertible in `F`: every
character of `A` extends along an injection `A ⟶ B`, because `μₙ` is then an injective
`ZMod n`-module (`baer_muNRep`). -/
theorem tateDualMap_surjective_of_injective (hn : IsUnit (n : F)) {A B : GalRep n F} {f : A ⟶ B}
    (hf : Function.Injective f.hom) : Function.Surjective (tateDualMap f).hom := by
  rw [coe_tateDualMap_hom]
  exact InternalHom.precomp_surjective_of_baer (baer_muNRep hn)
    (fun b : B.V => by rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]) hf

/-- **The Tate dual of a short exact sequence is short exact** when `n` is invertible in `F`: for
`0 → A → B → C → 0` exact, `0 → C' → B' → A' → 0` is exact. -/
theorem tateDualMap_exact (hn : IsUnit (n : F)) {A B C : GalRep n F} {f : A ⟶ B} {g : B ⟶ C}
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom)
    (hg : Function.Surjective g.hom) :
    Function.Injective (tateDualMap g).hom ∧
      Function.Exact (tateDualMap g).hom (tateDualMap f).hom ∧
        Function.Surjective (tateDualMap f).hom :=
  ⟨tateDualMap_injective_of_surjective hg, exact_tateDualMap hfg hg,
    tateDualMap_surjective_of_injective hn hf⟩

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

/-- Transport along `k = 2` of continuous cohomology classes is additive. -/
private theorem cast_continuousCohomology_add {k : ℕ} (h : k = 2)
    (u v : _root_.continuousCohomology.{0, u, u} k (muNRep n F)) :
    (h ▸ (u + v) : _root_.continuousCohomology.{0, u, u} 2 (muNRep n F)) = h ▸ u + h ▸ v := by
  subst h
  rfl

/-- Transport along `k = 2` of continuous cohomology classes preserves zero. -/
private theorem cast_continuousCohomology_zero {k : ℕ} (h : k = 2) :
    (h ▸ (0 : _root_.continuousCohomology.{0, u, u} k (muNRep n F)) :
      _root_.continuousCohomology.{0, u, u} 2 (muNRep n F)) = 0 := by
  subst h
  rfl

section PairingAPI

variable (A : GalRep n F) [DiscreteTopology A.V]
  (tr : _root_.continuousCohomology.{0, u, u} 2 (muNRep n F) ≃+ ZMod n)
  (i j : ℕ) (hij : i + j = 2)

/-- The local Tate-duality pairing is the chosen invariant of the evaluation cup product. -/
theorem tateDualityPairing_def (x : _root_.continuousCohomology.{0, u, u} i (tateDual A))
    (y : _root_.continuousCohomology.{0, u, u} j A) :
    tateDualityPairing A tr i j hij x y =
      tr (hij ▸ TopPairing.cup.{0, u, u} (tateEvaluationPairing A) i j x y) := by
  rw [tateDualityPairing]

/-- The local Tate-duality pairing is additive in its first argument. -/
theorem tateDualityPairing_add_left (x x' : _root_.continuousCohomology.{0, u, u} i (tateDual A))
    (y : _root_.continuousCohomology.{0, u, u} j A) :
    tateDualityPairing A tr i j hij (x + x') y =
      tateDualityPairing A tr i j hij x y + tateDualityPairing A tr i j hij x' y := by
  rw [tateDualityPairing_def, map_add, LinearMap.add_apply, cast_continuousCohomology_add,
    map_add, tateDualityPairing_def, tateDualityPairing_def]

/-- The local Tate-duality pairing is additive in its second argument. -/
theorem tateDualityPairing_add_right (x : _root_.continuousCohomology.{0, u, u} i (tateDual A))
    (y y' : _root_.continuousCohomology.{0, u, u} j A) :
    tateDualityPairing A tr i j hij x (y + y') =
      tateDualityPairing A tr i j hij x y + tateDualityPairing A tr i j hij x y' := by
  rw [tateDualityPairing_def, map_add, cast_continuousCohomology_add, map_add,
    tateDualityPairing_def, tateDualityPairing_def]

/-- The local Tate-duality pairing vanishes when its first argument is zero. -/
@[simp]
theorem tateDualityPairing_zero_left (y : _root_.continuousCohomology.{0, u, u} j A) :
    tateDualityPairing A tr i j hij 0 y = 0 := by
  rw [tateDualityPairing_def, map_zero, LinearMap.zero_apply, cast_continuousCohomology_zero,
    map_zero]

/-- The local Tate-duality pairing vanishes when its second argument is zero. -/
@[simp]
theorem tateDualityPairing_zero_right (x : _root_.continuousCohomology.{0, u, u} i (tateDual A)) :
    tateDualityPairing A tr i j hij x 0 = 0 := by
  rw [tateDualityPairing_def, map_zero, cast_continuousCohomology_zero, map_zero]

end PairingAPI

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
        simp only [LinearMap.compl₂_apply, ContinuousLinearMap.coe_coe,
          ContIntertwiningMap.toContinuousLinearMap_apply, TopRep.hom_comm_apply]
        exact (tateEvaluationPairing B).equivariant g ψ (f.hom a) }
  have h₁ := (hid _ (i + j) _).symm.trans (Q.cup_coeffMap (tateEvaluationPairing A)
    (tateDualMap f) (𝟙 _) (𝟙 _)
    (fun ψ a => (tateEvaluationPairing_tateDualMap f ψ a).symm) i j x y)
  have h₂ := (hid _ (i + j) _).symm.trans (Q.cup_coeffMap (tateEvaluationPairing B)
    (𝟙 _) f (𝟙 _) (fun _ _ => rfl) i j x y)
  simp only [hid] at h₁ h₂
  simp only [tateDualityPairing]
  rw [← h₁, ← h₂]

/-- **The Tate pairing transported along a curried pairing**: for a pairing `P : A × B → μₙ`,
pairing the image of `x` under `A → B'` with `y` is the chosen invariant of `P.cup x y`. -/
theorem tateDualityPairing_pairingToTateDual {A B : GalRep n F}
    [DiscreteTopology A.V] [DiscreteTopology B.V] (P : TopPairing A B (muNRep n F))
    (tr : _root_.continuousCohomology.{0, u, u} 2 (muNRep n F) ≃+ ZMod n)
    (i j : ℕ) (hij : i + j = 2)
    (x : _root_.continuousCohomology.{0, u, u} i A)
    (y : _root_.continuousCohomology.{0, u, u} j B) :
    tateDualityPairing B tr i j hij
        ((ContinuousCohomology.coeffMap (pairingToTateDual P) i).hom x) y =
      tr (hij ▸ TopPairing.cup.{0, u, u} P i j x y) := by
  have hcup := P.cup_coeffMap (tateEvaluationPairing B) (pairingToTateDual P) (𝟙 _) (𝟙 _)
    (fun a b => by
      rw [TopRep.id_apply, TopRep.id_apply, tateEvaluationPairing_bil,
        tateDualEquiv_pairingToTateDual_apply]) i j x y
  simp only [ContinuousCohomology.coeffMap_id, CategoryTheory.id_apply] at hcup
  rw [tateDualityPairing_def, hcup]

end TauCeti.ClassFieldTheory
