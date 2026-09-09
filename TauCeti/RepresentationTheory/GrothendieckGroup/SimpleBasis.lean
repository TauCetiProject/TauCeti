/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Category.ModuleCat.CartanMap
public import TauCeti.RingTheory.CompositionSeries.Additivity

/-!
# Simple classes in the Grothendieck group of finite-length modules

Let `R` be an Artinian ring. Every finitely generated left `R`-module has finite length, and its
Jordan--Hölder multiplicities are additive in short exact sequences. Consequently, multiplicity
of a fixed simple module descends to an integer-valued coordinate on the exact Grothendieck group
`G₀(mod R)`.

These coordinates show that the classes of any pairwise nonisomorphic family of simple modules
are linearly independent. If the family contains a representative of every simple finitely
generated module, finite-length induction also shows that the classes span, giving a canonical
`\mathbb Z`-basis of `G₀(mod R)` indexed by that family. The basis is the simple-module side of
the projective/simple coordinates used to express the Cartan map as a matrix.

## Main definitions

* `TauCeti.jordanHolderCoordinate`: the homomorphism from `G₀(mod R)` which reads the
  Jordan--Hölder multiplicity of a fixed simple module.
* `TauCeti.simpleClassBasis`: the basis of `G₀(mod R)` given by an exhaustive family of
  pairwise nonisomorphic simple modules.

## Main results

* `TauCeti.jordanHolderCoordinate_of`: the coordinate of an object class is its
  Jordan--Hölder multiplicity.
* `TauCeti.linearIndependent_exactK0OfFamily`: pairwise nonisomorphic simple classes are
  linearly independent.
* `TauCeti.span_range_exactK0OfFamily_eq_top`: an exhaustive family of simple classes spans.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 6.
* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory
  of Associative Algebras I*, Chapter III, Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v

variable {R : Type u} [Ring R] [IsArtinianRing R]

/-! ### Jordan--Hölder coordinates -/

section Coordinate

variable (R) (S : Type u) [AddCommGroup S] [Module R S]

private noncomputable def jordanHolderInvariant :
    ExactK0.AdditiveInvariant (finiteModulesExactStructure R) ℤ where
  obj M := jordanHolderMultiplicity R M S
  map_iso {_ _} e := congrArg Int.ofNat
    (jordanHolderMultiplicity_eq_of_linearEquiv (FGModuleCat.isoToLinearEquiv e) S)
  map_conflation {T} hT := by
    have hshort := (finiteModulesExactStructure_conflation_iff R T).mp hT
    have hexact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hshort.exact
    exact_mod_cast jordanHolderMultiplicity_eq_add_of_exact T.f.hom.hom T.g.hom.hom
      hshort.moduleCat_injective_f hshort.moduleCat_surjective_g hexact

/-- The **Jordan--Hölder coordinate** of a fixed module `S` on `G₀(mod R)`. On the class of
`M` it is the multiplicity `[M : S]`. It is useful as a simple coordinate when `S` is simple, but
the construction is valid for arbitrary `S` (and is then identically zero if `S` is not simple). -/
noncomputable def jordanHolderCoordinate :
    ExactK0 (finiteModulesExactStructure R) →+ ℤ :=
  ExactK0.lift (jordanHolderInvariant R S)

/-- The Jordan--Hölder coordinate of an object class is its multiplicity in that module. -/
@[simp]
theorem jordanHolderCoordinate_of (M : FGModuleCat.{u} R) :
    jordanHolderCoordinate R S (ExactK0.of M) = jordanHolderMultiplicity R M S :=
  ExactK0.lift_of (jordanHolderInvariant R S) M

/-- Isomorphic modules define the same Jordan--Hölder coordinate. -/
theorem jordanHolderCoordinate_congr
    {T : Type u} [AddCommGroup T] [Module R T] (e : S ≃ₗ[R] T) :
    jordanHolderCoordinate R S = jordanHolderCoordinate R T := by
  refine ExactK0.hom_ext fun M ↦ ?_
  simp only [jordanHolderCoordinate_of]
  exact congrArg Int.ofNat (jordanHolderMultiplicity_congr e)

/-- A simple module has coordinate one on its own class. -/
@[simp high]
theorem jordanHolderCoordinate_self [IsSimpleModule R S] [Module.Finite R S] :
    jordanHolderCoordinate R S (ExactK0.of (FGModuleCat.of R S)) = 1 := by
  rw [jordanHolderCoordinate_of]
  exact_mod_cast jordanHolderMultiplicity_eq_one_of_isSimpleModule_of_linearEquiv S
    (LinearEquiv.refl R S)

/-- Two nonisomorphic simple modules have zero mutual Jordan--Hölder coordinate. -/
@[simp high]
theorem jordanHolderCoordinate_of_eq_zero_of_isEmpty_linearEquiv
    {T : Type u} [AddCommGroup T] [Module R T] [Module.Finite R T] [IsSimpleModule R T]
    (h : IsEmpty (T ≃ₗ[R] S)) :
    jordanHolderCoordinate R S (ExactK0.of (FGModuleCat.of R T)) = 0 := by
  rw [jordanHolderCoordinate_of]
  exact_mod_cast jordanHolderMultiplicity_eq_zero_of_isEmpty_linearEquiv_of_isSimpleModule S h

end Coordinate

/-! ### Linear independence and spanning -/

section SimpleFamily

variable {I : Type v} (S : I → FGModuleCat.{u} R)
variable [hS : ∀ i, IsSimpleModule R (S i)]

/-- The classes in `G₀(mod R)` of an indexed family of finitely generated modules. -/
noncomputable def exactK0OfFamily (i : I) : ExactK0 (finiteModulesExactStructure R) :=
  ExactK0.of (S i)

@[simp]
theorem jordanHolderCoordinate_exactK0OfFamily_self (i : I) :
    jordanHolderCoordinate R (S i) (exactK0OfFamily S i) = 1 :=
  jordanHolderCoordinate_self R (S i)

/-- A Jordan--Hölder coordinate is zero on a nonisomorphic member of a simple family. -/
theorem jordanHolderCoordinate_exactK0OfFamily_eq_zero {i j : I}
    (hij : IsEmpty ((S j : Type u) ≃ₗ[R] S i)) :
    jordanHolderCoordinate R (S i) (exactK0OfFamily S j) = 0 :=
  jordanHolderCoordinate_of_eq_zero_of_isEmpty_linearEquiv R (S i) hij

/-- On a pairwise nonisomorphic simple family, the Jordan--Hölder coordinates form the
Kronecker-delta matrix. -/
@[simp]
theorem jordanHolderCoordinate_exactK0OfFamily
    [DecidableEq I]
    (hnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[R] S j)) (i j : I) :
    jordanHolderCoordinate R (S i) (exactK0OfFamily S j) = if j = i then 1 else 0 := by
  classical
  by_cases hji : j = i
  · subst j
    simp
  · simp only [hji, ↓reduceIte]
    exact jordanHolderCoordinate_exactK0OfFamily_eq_zero S (hnoniso hji)

/-- **Pairwise nonisomorphic simple classes are linearly independent in `G₀(mod R)`.** -/
theorem linearIndependent_exactK0OfFamily
    (hnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[R] S j)) :
    LinearIndependent ℤ (exactK0OfFamily S) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (exactK0OfFamily S)
    (fun i ↦ (jordanHolderCoordinate R (S i)).toIntLinearMap)
  · intro i j hij
    exact jordanHolderCoordinate_exactK0OfFamily_eq_zero S (hnoniso hij.symm)
  · exact jordanHolderCoordinate_exactK0OfFamily_self S

variable (hnoniso : Pairwise fun i j ↦ IsEmpty ((S i : Type u) ≃ₗ[R] S j))

/-- A family of simple modules is exhaustive if every simple finitely generated module is
isomorphic to one of its members. -/
def IsExhaustiveSimpleFamily : Prop :=
  ∀ (M : FGModuleCat.{u} R), IsSimpleModule R M →
    ∃ i, Nonempty ((M : Type u) ≃ₗ[R] S i)

omit [IsArtinianRing R] hS in
/-- Unfolding lemma for `IsExhaustiveSimpleFamily`: its body is not exposed outside this
module, so consumers need this to build or use the predicate. -/
theorem isExhaustiveSimpleFamily_iff : IsExhaustiveSimpleFamily S ↔
    ∀ (M : FGModuleCat.{u} R), IsSimpleModule R M →
      ∃ i, Nonempty ((M : Type u) ≃ₗ[R] S i) :=
  (Iff.rfl)

omit hS in
private theorem exactK0_of_type_mem_span_range_simple
    (hexhaustive : IsExhaustiveSimpleFamily S)
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ExactK0.of (FGModuleCat.of R M) ∈
      Submodule.span ℤ (Set.range (exactK0OfFamily S)) := by
  let G := Submodule.span ℤ (Set.range (exactK0OfFamily S))
  have hfinite : IsFiniteLength R M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine IsFiniteLength.rec (motive := fun (M : Type u) [AddCommGroup M] [Module R M] _ ↦
      ∀ hM : Module.Finite R M,
        ExactK0.of (@FGModuleCat.of R _ M _ _ hM) ∈ G) ?_ ?_ hfinite inferInstance
  · intro M _ _ _ hM
    let _ : Module.Finite R M := hM
    have hzero : IsZero (FGModuleCat.of R M) := IsZero.of_full_of_faithful_of_isZero
        (ModuleCat.isFG R).ι (FGModuleCat.of R M)
          (ModuleCat.isZero_of_subsingleton (ModuleCat.of R M))
    rw [ExactK0.of_eq_zero_of_isZero hzero]
    exact G.zero_mem
  · intro M _ _ N _ hN ih hM
    let _ : Module.Finite R M := hM
    let _ : IsNoetherian R N :=
        (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
    let _ : IsArtinian R N :=
        (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2
    let _ : Module.Finite R N := inferInstance
    let Q := M ⧸ N
    let _ : IsSimpleModule R Q := inferInstance
    let _ : Module.Finite R Q := inferInstance
    obtain ⟨i, ⟨e⟩⟩ := hexhaustive (FGModuleCat.of R Q) inferInstance
    have hQ : ExactK0.of (FGModuleCat.of R Q) ∈ G := by
      rw [ExactK0.of_congr e.toFGModuleCatIso]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hNmem : ExactK0.of (FGModuleCat.of R N) ∈ G := ih inferInstance
    let T : ShortComplex (FGModuleCat R) :=
      ShortComplex.mk (FGModuleCat.ofHom N.subtype) (FGModuleCat.ofHom N.mkQ) (by
        apply FGModuleCat.hom_ext
        exact (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero)
    have hconf : (finiteModulesExactStructure R).Conflation T :=
      (finiteModulesExactStructure_conflation_iff R T).mpr <| by
        apply ModuleCat.shortComplex_shortExact
        · exact LinearMap.exact_subtype_mkQ N
        · exact N.injective_subtype
        · exact N.mkQ_surjective
    have hrel :
        (ExactK0.of (FGModuleCat.of R M) : ExactK0 (finiteModulesExactStructure R)) =
          ExactK0.of (FGModuleCat.of R N) + ExactK0.of (FGModuleCat.of R Q) := by
      simpa only [T, Q] using ExactK0.of_conflation hconf
    rw [hrel]
    exact G.add_mem hNmem hQ

omit hS in
private theorem exactK0_of_mem_span_range_simple
    (hexhaustive : IsExhaustiveSimpleFamily S) (M : FGModuleCat.{u} R) :
    ExactK0.of M ∈ Submodule.span ℤ (Set.range (exactK0OfFamily S)) :=
  exactK0_of_type_mem_span_range_simple S hexhaustive

omit hS in
/-- **An exhaustive family of simple classes spans `G₀(mod R)`.** Every finitely generated
module over an Artinian ring has finite length, and induction on a simple-quotient filtration
expresses its class as a sum of simple classes. -/
theorem span_range_exactK0OfFamily_eq_top
    (hexhaustive : IsExhaustiveSimpleFamily S) :
    Submodule.span ℤ (Set.range (exactK0OfFamily S)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using ExactK0.induction_on with
  | zero => exact Submodule.zero_mem _
  | of M => exact exactK0_of_mem_span_range_simple S hexhaustive M
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | neg x hx => exact Submodule.neg_mem _ hx

/-- **The simple-class basis of `G₀(mod R)`.** Its basis vector at `i` is the class `[S i]`.
The hypotheses say precisely that the chosen modules are simple, pairwise nonisomorphic, and
exhaust all simple finitely generated modules. -/
noncomputable def simpleClassBasis (hexhaustive : IsExhaustiveSimpleFamily S) :
    Module.Basis I ℤ (ExactK0 (finiteModulesExactStructure R)) :=
  Module.Basis.mk (linearIndependent_exactK0OfFamily S hnoniso)
    (span_range_exactK0OfFamily_eq_top S hexhaustive).ge

/-- The basis vector indexed by `i` is the Grothendieck class `[S i]`. -/
@[simp]
theorem simpleClassBasis_apply (hexhaustive : IsExhaustiveSimpleFamily S) (i : I) :
    simpleClassBasis S hnoniso hexhaustive i = ExactK0.of (S i) :=
  Module.Basis.mk_apply _ _ i

/-- The `i`th coefficient in the simple-class basis is the Jordan--Hölder multiplicity
coordinate attached to `S i`. -/
@[simp]
theorem simpleClassBasis_repr_apply (hexhaustive : IsExhaustiveSimpleFamily S)
    (x : ExactK0 (finiteModulesExactStructure R)) (i : I) :
    (simpleClassBasis S hnoniso hexhaustive).repr x i = jordanHolderCoordinate R (S i) x := by
  classical
  refine (simpleClassBasis S hnoniso hexhaustive).repr_apply_eq
    (fun x i ↦ jordanHolderCoordinate R (S i) x) (fun x y ↦ funext fun i ↦ map_add _ x y)
    (fun c x ↦ funext fun i ↦ map_zsmul _ c x) (fun j ↦ funext fun k ↦ ?_) x i
  rw [simpleClassBasis_apply, Finsupp.single_apply]
  exact jordanHolderCoordinate_exactK0OfFamily S hnoniso k j

end SimpleFamily

end TauCeti
