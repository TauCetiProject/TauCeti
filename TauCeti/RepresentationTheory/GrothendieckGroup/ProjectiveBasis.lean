/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Module
public import TauCeti.Algebra.Category.ModuleCat.CartanMap
public import TauCeti.RingTheory.KrullSchmidt.Multiplicity

/-!
# Indecomposable classes in the Grothendieck group of finitely generated projectives

Let `R` be an Artinian ring.  Every finitely generated `R`-module has finite length, so the
Krull-Schmidt theorem applies to it: it decomposes into indecomposable summands, uniquely up to a
matching.  The multiplicity of a fixed module among those summands is additive on direct sums, and
the exact structure of the finitely generated projectives is the split one, so that multiplicity
descends to an integer-valued coordinate on `K₀(proj R)`.

These coordinates show that the classes of any pairwise nonisomorphic family of indecomposable
finitely generated projective modules are linearly independent.  If the family contains a
representative of every indecomposable finitely generated projective, an induction on the length of
a module also shows that the classes span, giving a canonical `ℤ`-basis of `K₀(proj R)` indexed by
that family.  The basis is the projective side of the projective/simple coordinates that express
the Cartan map `TauCeti.cartanMap` as a matrix; the simple side is
`TauCeti.simpleClassBasis`, in `TauCeti/RepresentationTheory/GrothendieckGroup/SimpleBasis.lean`.

## Main definitions

* `TauCeti.indecomposableCoordinate`: the homomorphism from `K₀(proj R)` which reads the
  Krull-Schmidt multiplicity of a fixed module.
* `TauCeti.IsExhaustiveIndecomposableProjectiveFamily`: a family of finitely generated projective
  modules meeting every indecomposable one.
* `TauCeti.indecomposableProjectiveClassBasis`: the basis of `K₀(proj R)` given by an exhaustive
  family of pairwise nonisomorphic indecomposable finitely generated projective modules.

## Main results

* `TauCeti.indecomposableCoordinate_of`: the coordinate of an object class is its Krull-Schmidt
  multiplicity.
* `TauCeti.linearIndependent_exactK0_of`: pairwise nonisomorphic indecomposable projective classes
  are linearly independent.
* `TauCeti.span_range_exactK0_of_eq_top`: an exhaustive family of indecomposable projective classes
  spans.
* `TauCeti.isExhaustiveIndecomposableProjectiveFamily_of_isLocalRing`: over a commutative local
  ring the ring itself is, up to isomorphism, the only indecomposable finitely generated
  projective module.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Sections 5
  and 7.
* Ibrahim Assem, Daniel Simson, and Andrzej Skowroński, *Elements of the Representation Theory
  of Associative Algebras I*, Chapter I, Section 4, and Chapter III, Section 3.
* The construction and proof architecture are adapted from
  `TauCeti/RepresentationTheory/GrothendieckGroup/SimpleBasis.lean`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u w w'

variable {R : Type u} [Ring R] [IsArtinianRing R]

/-! ### The multiplicity coordinates -/

section Coordinate

variable (R) (N : Type w) [AddCommGroup N] [Module R N]

/-- The Krull-Schmidt multiplicity of `N`, as an invariant of finitely generated projective
modules.  It is additive on conflations because a conflation of finitely generated projectives is a
split short exact sequence of modules. -/
private noncomputable def indecomposableInvariant :
    ExactK0.AdditiveInvariant (finiteProjectiveModulesExactStructure R) ℤ where
  obj X := (indecomposableMultiplicity R X.obj N : ℤ)
  map_iso {X Y} e := congrArg Int.ofNat (indecomposableMultiplicity_eq_of_linearEquiv
    (M := X.obj) (M' := Y.obj) ((finiteProjectiveModules R).ι.mapIso e).toLinearEquiv)
  map_conflation {S} hS := by
    have hT := (finiteProjectiveModulesExactStructure_conflation_iff R S).mp hS
    -- Instance search is keyed on the head symbol, so the instances carried by the objects of the
    -- subcategory have to be restated for the terms of the short complex mapped into `ModuleCat`.
    have : Module.Projective R (S.map (finiteProjectiveModules R).ι).X₃ :=
      inferInstanceAs (Module.Projective R S.X₃.obj)
    have : IsNoetherian R (S.map (finiteProjectiveModules R).ι).X₁ :=
      inferInstanceAs (IsNoetherian R S.X₁.obj)
    have : IsArtinian R (S.map (finiteProjectiveModules R).ι).X₁ :=
      inferInstanceAs (IsArtinian R S.X₁.obj)
    have : IsNoetherian R (S.map (finiteProjectiveModules R).ι).X₃ :=
      inferInstanceAs (IsNoetherian R S.X₃.obj)
    have : IsArtinian R (S.map (finiteProjectiveModules R).ι).X₃ :=
      inferInstanceAs (IsArtinian R S.X₃.obj)
    obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective
      (S.map (finiteProjectiveModules R).ι).g.hom
      (LinearMap.range_eq_top.mpr hT.moduleCat_surjective_g)
    exact congrArg Int.ofNat (indecomposableMultiplicity_eq_add_of_exact_of_rightInverse
      hT.moduleCat_injective_f
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hT.exact)
      fun x ↦ DFunLike.congr_fun hσ x)

/-- **The Krull-Schmidt coordinate** of a fixed module `N` on `K₀(proj R)`.  On the class of a
finitely generated projective module `M` it is the number of summands of `M` isomorphic to `N` in a
decomposition of `M` into indecomposables.  It is useful as a coordinate when `N` is indecomposable,
but the construction is valid for arbitrary `N` (and is identically zero when `N` is not
indecomposable, by `TauCeti.isIndecomposableModule_of_indecomposableMultiplicity_ne_zero`). -/
noncomputable def indecomposableCoordinate :
    ExactK0.{u} (finiteProjectiveModulesExactStructure R) →+ ℤ :=
  ExactK0.lift (indecomposableInvariant R N)

/-- The coordinate of an object class is its Krull-Schmidt multiplicity. -/
@[simp]
theorem indecomposableCoordinate_of (X : (finiteProjectiveModules R).FullSubcategory) :
    indecomposableCoordinate R N (ExactK0.of X) = indecomposableMultiplicity R X.obj N :=
  ExactK0.lift_of _ _

/-- Linearly equivalent modules define the same Krull-Schmidt coordinate. -/
theorem indecomposableCoordinate_congr
    {N' : Type w'} [AddCommGroup N'] [Module R N'] (e : N ≃ₗ[R] N') :
    indecomposableCoordinate R N = indecomposableCoordinate R N' := by
  refine ExactK0.hom_ext fun X ↦ ?_
  simp only [indecomposableCoordinate_of]
  exact congrArg Int.ofNat (indecomposableMultiplicity_congr e)

end Coordinate

/-- An indecomposable module has coordinate one on its own class. -/
@[simp high]
theorem indecomposableCoordinate_self (X : (finiteProjectiveModules R).FullSubcategory)
    (hX : IsIndecomposableModule R X.obj) :
    indecomposableCoordinate R X.obj (ExactK0.of X) = 1 := by
  rw [indecomposableCoordinate_of]
  exact_mod_cast indecomposableMultiplicity_self hX (LinearEquiv.refl R _)

/-- Two nonisomorphic indecomposable modules have zero mutual coordinate. -/
@[simp high]
theorem indecomposableCoordinate_eq_zero_of_isEmpty_linearEquiv
    (X Y : (finiteProjectiveModules R).FullSubcategory)
    (hY : IsIndecomposableModule R Y.obj) (h : IsEmpty (↥Y.obj ≃ₗ[R] ↥X.obj)) :
    indecomposableCoordinate R X.obj (ExactK0.of Y) = 0 := by
  rw [indecomposableCoordinate_of]
  exact_mod_cast indecomposableMultiplicity_eq_zero_of_isEmpty_linearEquiv hY h

/-! ### Linear independence and spanning -/

section Family

variable {I : Type*} (P : I → (finiteProjectiveModules R).FullSubcategory)

/-- **Pairwise nonisomorphic indecomposable projective classes are linearly independent in
`K₀(proj R)`.** -/
theorem linearIndependent_exactK0_of
    (hind : ∀ i, IsIndecomposableModule R (P i).obj)
    (hnoniso : Pairwise fun i j ↦ IsEmpty (↥(P i).obj ≃ₗ[R] ↥(P j).obj)) :
    LinearIndependent ℤ fun i ↦ (ExactK0.of (P i) :
      ExactK0.{u} (finiteProjectiveModulesExactStructure R)) := by
  refine LinearIndependent.of_pairwise_dual_eq_zero_one
    (fun i ↦ (ExactK0.of (P i) : ExactK0.{u} (finiteProjectiveModulesExactStructure R)))
    (fun i ↦ (indecomposableCoordinate R ↥(P i).obj).toIntLinearMap) ?_ ?_
  · intro i j hij
    exact indecomposableCoordinate_eq_zero_of_isEmpty_linearEquiv _ _ (hind j) (hnoniso hij.symm)
  · intro i
    exact indecomposableCoordinate_self _ (hind i)

/-- A family of finitely generated projective modules is exhaustive if every indecomposable
finitely generated projective module is isomorphic to one of its members. -/
def IsExhaustiveIndecomposableProjectiveFamily : Prop :=
  ∀ X : (finiteProjectiveModules R).FullSubcategory, IsIndecomposableModule R X.obj →
    ∃ i, Nonempty (↥X.obj ≃ₗ[R] ↥(P i).obj)

omit [IsArtinianRing R] in
/-- Characterization of `TauCeti.IsExhaustiveIndecomposableProjectiveFamily`: the family is
exhaustive exactly when every indecomposable finitely generated projective module is isomorphic to
one of its members.  Importing modules build and use the predicate through this lemma, since the
body of the definition above is not exposed to them. -/
theorem isExhaustiveIndecomposableProjectiveFamily_iff :
    IsExhaustiveIndecomposableProjectiveFamily P ↔
      ∀ X : (finiteProjectiveModules R).FullSubcategory, IsIndecomposableModule R X.obj →
        ∃ i, Nonempty (↥X.obj ≃ₗ[R] ↥(P i).obj) :=
  (Iff.rfl)

/-- Splitting off one indecomposable summand at a time expresses the class of a finitely generated
projective module of length at most `n` in terms of the exhaustive family.  Each step replaces the
module by a complement of an indecomposable summand, whose length is strictly smaller. -/
private theorem mem_span_of_length_le
    (hexh : IsExhaustiveIndecomposableProjectiveFamily P) (n : ℕ) :
    ∀ X : (finiteProjectiveModules R).FullSubcategory, Module.length R X.obj ≤ n →
      (ExactK0.of X : ExactK0.{u} (finiteProjectiveModulesExactStructure R)) ∈
        Submodule.span ℤ (Set.range fun i ↦
          (ExactK0.of (P i) : ExactK0.{u} (finiteProjectiveModulesExactStructure R))) := by
  have hzero : ∀ X : (finiteProjectiveModules R).FullSubcategory, Subsingleton X.obj →
      (ExactK0.of X : ExactK0.{u} (finiteProjectiveModulesExactStructure R)) ∈
        Submodule.span ℤ (Set.range fun i ↦
          (ExactK0.of (P i) : ExactK0.{u} (finiteProjectiveModulesExactStructure R))) := by
    intro X hX
    convert Submodule.zero_mem _ using 1
    exact ExactK0.of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
      (finiteProjectiveModules R).ι X (ModuleCat.isZero_of_subsingleton X.obj))
  induction n with
  | zero =>
    intro X hX
    exact hzero X (Module.length_eq_zero_iff.mp (le_antisymm (by simpa using hX) zero_le))
  | succ n ih =>
    intro X hX
    rcases subsingleton_or_nontrivial (X.obj : Type u) with hsub | hnt
    · exact hzero X hsub
    obtain ⟨T, T', hcompl, hTind⟩ := exists_isCompl_isIndecomposableModule (A := R) (M := X.obj)
    have hTproj : Module.Projective R T :=
      Module.Projective.of_split T.subtype (T.projectionOnto T' hcompl) (by ext x; simp)
    have hT'proj : Module.Projective R T' :=
      Module.Projective.of_split T'.subtype (T'.projectionOnto T hcompl.symm) (by ext x; simp)
    set XT : (finiteProjectiveModules R).FullSubcategory :=
      ⟨ModuleCat.of R T, finiteProjectiveModules_iff.mpr ⟨inferInstance, hTproj⟩⟩ with hXTdef
    set XT' : (finiteProjectiveModules R).FullSubcategory :=
      ⟨ModuleCat.of R T', finiteProjectiveModules_iff.mpr ⟨inferInstance, hT'proj⟩⟩ with hXT'def
    have hker : LinearMap.ker (T'.projectionOnto T hcompl.symm) = T := by
      ext x
      simp
    have hex : Function.Exact T.subtype (T'.projectionOnto T hcompl.symm) :=
      LinearMap.exact_iff.mpr (by rw [hker, Submodule.range_subtype])
    set f : XT ⟶ X := ObjectProperty.homMk (ModuleCat.ofHom T.subtype) with hfdef
    set g : X ⟶ XT' :=
      ObjectProperty.homMk (ModuleCat.ofHom (T'.projectionOnto T hcompl.symm)) with hgdef
    have hzeroc : f ≫ g = 0 := by
      refine ObjectProperty.hom_ext _ (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
      exact (Submodule.projectionOnto_apply_eq_zero_iff hcompl.symm).mpr x.2
    have hconf : (finiteProjectiveModulesExactStructure R).Conflation
        (ShortComplex.mk f g hzeroc) := by
      rw [finiteProjectiveModulesExactStructure_conflation_iff]
      apply ModuleCat.shortComplex_shortExact
      · exact hex
      · exact T.injective_subtype
      · exact Submodule.projectionOnto_surjective hcompl.symm
    have hsum := ExactK0.of_conflation.{u, u, u + 1} hconf
    have hTmem : (ExactK0.of XT : ExactK0.{u} (finiteProjectiveModulesExactStructure R)) ∈
        Submodule.span ℤ (Set.range fun i ↦
          (ExactK0.of (P i) : ExactK0.{u} (finiteProjectiveModulesExactStructure R))) := by
      obtain ⟨i, ⟨e⟩⟩ := hexh XT hTind
      rw [ExactK0.of_congr.{u, u, u + 1}
        (((finiteProjectiveModules R).fullyFaithfulι).preimageIso
          (X := XT) (Y := P i) e.toModuleIso)]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hlen : Module.length R T' ≤ (n : ℕ∞) := by
      have hne : T' ≠ ⊤ := by
        rintro rfl
        exact (Submodule.nontrivial_iff_ne_bot.mp hTind.nontrivial)
          (disjoint_top.mp hcompl.disjoint)
      have h1 := (Submodule.length_lt (R := R) (M := X.obj) hne).trans_le hX
      rw [Nat.cast_add, Nat.cast_one, ENat.lt_add_one_iff (ENat.natCast_ne_top n)] at h1
      exact h1
    have hmem := Submodule.add_mem _ hTmem (ih XT' hlen)
    rw [← hsum] at hmem
    exact hmem

/-- **An exhaustive family of indecomposable projective classes spans `K₀(proj R)`.**  Every
finitely generated module over an Artinian ring has finite length, and splitting off one
indecomposable summand at a time expresses the class of a finitely generated projective module as a
sum of indecomposable projective classes. -/
theorem span_range_exactK0_of_eq_top (hexh : IsExhaustiveIndecomposableProjectiveFamily P) :
    Submodule.span ℤ (Set.range fun i ↦
        (ExactK0.of (P i) : ExactK0.{u} (finiteProjectiveModulesExactStructure R))) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using ExactK0.induction_on with
  | zero => exact Submodule.zero_mem _
  | of X =>
    exact mem_span_of_length_le P hexh (Module.length R X.obj).toNat X
      (by rw [ENat.natCast_toNat Module.length_ne_top])
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | neg x hx => exact Submodule.neg_mem _ hx

/-- **The indecomposable-projective basis of `K₀(proj R)`.**  Its basis vector at `i` is the class
`[P i]`.  The hypotheses say precisely that the chosen modules are indecomposable, pairwise
nonisomorphic, and exhaust all indecomposable finitely generated projective modules. -/
noncomputable def indecomposableProjectiveClassBasis
    (hind : ∀ i, IsIndecomposableModule R (P i).obj)
    (hnoniso : Pairwise fun i j ↦ IsEmpty (↥(P i).obj ≃ₗ[R] ↥(P j).obj))
    (hexh : IsExhaustiveIndecomposableProjectiveFamily P) :
    Module.Basis I ℤ (ExactK0.{u} (finiteProjectiveModulesExactStructure R)) :=
  Module.Basis.mk (linearIndependent_exactK0_of P hind hnoniso)
    (span_range_exactK0_of_eq_top P hexh).ge

/-- The basis vector indexed by `i` is the Grothendieck class `[P i]`. -/
@[simp]
theorem indecomposableProjectiveClassBasis_apply
    (hind : ∀ i, IsIndecomposableModule R (P i).obj)
    (hnoniso : Pairwise fun i j ↦ IsEmpty (↥(P i).obj ≃ₗ[R] ↥(P j).obj))
    (hexh : IsExhaustiveIndecomposableProjectiveFamily P) (i : I) :
    indecomposableProjectiveClassBasis P hind hnoniso hexh i =
      (ExactK0.of (P i) : ExactK0.{u} (finiteProjectiveModulesExactStructure R)) :=
  Module.Basis.mk_apply _ _ i

/-- The `i`th coefficient in the indecomposable-projective basis is the Krull-Schmidt multiplicity
coordinate attached to `P i`. -/
@[simp]
theorem indecomposableProjectiveClassBasis_repr_apply
    (hind : ∀ i, IsIndecomposableModule R (P i).obj)
    (hnoniso : Pairwise fun i j ↦ IsEmpty (↥(P i).obj ≃ₗ[R] ↥(P j).obj))
    (hexh : IsExhaustiveIndecomposableProjectiveFamily P)
    (x : ExactK0.{u} (finiteProjectiveModulesExactStructure R)) (i : I) :
    (indecomposableProjectiveClassBasis P hind hnoniso hexh).repr x i =
      indecomposableCoordinate R ↥(P i).obj x := by
  classical
  refine (indecomposableProjectiveClassBasis P hind hnoniso hexh).repr_apply_eq
    (fun x i ↦ indecomposableCoordinate R ↥(P i).obj x) (fun x y ↦ funext fun i ↦ map_add _ x y)
    (fun c x ↦ funext fun i ↦ map_zsmul _ c x) (fun j ↦ funext fun k ↦ ?_) x i
  rw [indecomposableProjectiveClassBasis_apply, Finsupp.single_apply, indecomposableCoordinate_of]
  exact_mod_cast indecomposableMultiplicity_eq_ite (P := fun i ↦ ↥(P i).obj) hind hnoniso k j

end Family

/-! ### Commutative local rings -/

section IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- **Over a commutative local ring, one projective module isomorphic to the ring is an exhaustive
family**: a finitely generated projective module over such a ring is free, and an indecomposable
free module is isomorphic to the ring. -/
theorem isExhaustiveIndecomposableProjectiveFamily_of_isLocalRing
    (X : (finiteProjectiveModules A).FullSubcategory) (e : X.obj ≃ₗ[A] A) :
    IsExhaustiveIndecomposableProjectiveFamily fun _ : Unit ↦ X := by
  refine (isExhaustiveIndecomposableProjectiveFamily_iff _).2 fun Y hY ↦ ⟨(), ?_⟩
  have : Module.Free A Y.obj := Module.free_of_flat_of_isLocalRing
  obtain ⟨e'⟩ := hY.nonempty_linearEquiv_of_free
  exact ⟨e'.trans e.symm⟩

end IsLocalRing

end TauCeti
