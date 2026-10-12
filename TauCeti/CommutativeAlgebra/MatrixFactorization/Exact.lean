/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CommutativeAlgebra.MatrixFactorization.Biproduct
public import TauCeti.Algebra.Homology.Curved.Exact
public import TauCeti.CategoryTheory.Exact.ExtensionClosed

/-!
# The componentwise split exact structure on matrix factorizations

Finite-projective matrix factorizations form an extension-closed full subcategory of curved
duplexes of finitely generated modules with the componentwise split exact structure.
The induced conflations split in each parity, but their splittings need not commute with the
differentials. A componentwise split conflation with finite-projective middle term also has
finite-projective outer terms. Consequently the disk presentations stay in this subcategory.

This is the exact structure used to identify the stable category with the matrix-factorization
homotopy category. It follows Frenkel, Khovanov and Schiffmann, *Homological realization of
Nakajima varieties and Weyl group actions*, Sections 2–3; the finite-projective formulation
follows Orlov, *Triangulated categories of singularities and D-branes in Landau–Ginzburg
models*, Sections 1.2 and 3. The construction reuses `ExactStructure.fullSubcategory` and the
componentwise exact structure on curved duplexes.
-/

public section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory CategoryTheory.Limits

variable {S : Type u} [CommRing S] {w : S}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- Finite-projective duplexes are closed under componentwise split extensions. -/
theorem isExtensionClosed_isProjective :
    ((ExactStructure.split (FGModuleCat.{u} S)).curvedDuplex w).IsExtensionClosed
      (isProjective S w) where
  prop_X₂ {T} hT h₁ h₃ := by
    rw [ExactStructure.curvedDuplex_conflation_iff] at hT
    obtain ⟨s₀⟩ := (ExactStructure.split_conflation _).mp hT.1
    obtain ⟨s₁⟩ := (ExactStructure.split_conflation _).mp hT.2
    dsimp only [ShortComplex.map, CurvedDuplex.eval₀] at s₀
    dsimp only [ShortComplex.map, CurvedDuplex.eval₁] at s₁
    let := h₁.1
    let := h₁.2
    let := h₃.1
    let := h₃.2
    have := FGModuleCat.projective_biprod S T.X₁.X₀ T.X₃.X₀
    have := FGModuleCat.projective_biprod S T.X₁.X₁ T.X₃.X₁
    exact ⟨Module.Projective.of_equiv' (FGModuleCat.isoToLinearEquiv s₀.isoBinaryBiproduct).symm,
      Module.Projective.of_equiv' (FGModuleCat.isoToLinearEquiv s₁.isoBinaryBiproduct).symm⟩

/-- The finite-projective subcategory contains a zero duplex. -/
instance containsZero_isProjective : (isProjective S w).ContainsZero where
  exists_zero := ⟨zero.obj, (inclusion (S := S) (w := w)).map_isZero isZero_zero,
    zero.property⟩

/-- Finite projectivity of the two components is invariant under duplex isomorphisms. -/
instance isClosedUnderIsomorphisms_isProjective :
    (isProjective S w).IsClosedUnderIsomorphisms :=
  isExtensionClosed_isProjective.isClosedUnderIsomorphisms

/-- The finite-projective subcategory is closed under binary products. -/
instance isClosedUnderBinaryProducts_isProjective :
    (isProjective S w).IsClosedUnderBinaryProducts :=
  isExtensionClosed_isProjective.isClosedUnderBinaryProducts

/-- In a componentwise split conflation, projectivity of the middle components implies
projectivity of both outer components, since each is a direct summand of the middle one. -/
theorem isProjective_outer_of_conflation
    {T : ShortComplex (CurvedDuplex (FGModuleCat.{u} S) w)}
    (hT : ((ExactStructure.split (FGModuleCat.{u} S)).curvedDuplex w).Conflation T)
    (h₂ : isProjective S w T.X₂) : isProjective S w T.X₁ ∧ isProjective S w T.X₃ := by
  rw [ExactStructure.curvedDuplex_conflation_iff] at hT
  obtain ⟨s₀⟩ := (ExactStructure.split_conflation _).mp hT.1
  obtain ⟨s₁⟩ := (ExactStructure.split_conflation _).mp hT.2
  dsimp only [ShortComplex.map, CurvedDuplex.eval₀] at s₀
  dsimp only [ShortComplex.map, CurvedDuplex.eval₁] at s₁
  let := h₂.1
  let := h₂.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply Module.Projective.of_split T.f.f₀.hom.hom s₀.r.hom.hom
    exact congrArg (fun f ↦ f.hom.hom) s₀.f_r
  · apply Module.Projective.of_split T.f.f₁.hom.hom s₁.r.hom.hom
    exact congrArg (fun f ↦ f.hom.hom) s₁.f_r
  · apply Module.Projective.of_split s₀.s.hom.hom T.g.f₀.hom.hom
    exact congrArg (fun f ↦ f.hom.hom) s₀.s_g
  · apply Module.Projective.of_split s₁.s.hom.hom T.g.f₁.hom.hom
    exact congrArg (fun f ↦ f.hom.hom) s₁.s_g

variable (S w)

/-- The exact structure on finite-projective matrix factorizations whose conflations split
on each underlying module, without requiring differential-compatible splittings. -/
noncomputable def splitExact : ExactStructure (MatrixFactorization S w) :=
  ((ExactStructure.split (FGModuleCat.{u} S)).curvedDuplex w).fullSubcategory
    (isProjective S w) isExtensionClosed_isProjective

/-- The componentwise split structure is induced from the ambient curved-duplex structure. -/
theorem splitExact_def :
    splitExact S w =
      ((ExactStructure.split (FGModuleCat.{u} S)).curvedDuplex w).fullSubcategory
        (isProjective S w) isExtensionClosed_isProjective := (rfl)

variable {S w}

/-- A conflation of matrix factorizations is precisely a short complex admitting a splitting
in each parity. -/
@[simp] theorem splitExact_conflation_iff (T : ShortComplex (MatrixFactorization S w)) :
    (splitExact S w).Conflation T ↔
      Nonempty ((T.map inclusion).map (CurvedDuplex.eval₀ (FGModuleCat.{u} S) w)).Splitting ∧
      Nonempty ((T.map inclusion).map (CurvedDuplex.eval₁ (FGModuleCat.{u} S) w)).Splitting := by
  simp [splitExact, ExactStructure.split_conflation]

/-- The finite-projective inclusion preserves componentwise split conflations. -/
theorem isConflationExact_inclusion :
    (splitExact S w).IsConflationExact
      ((ExactStructure.split (FGModuleCat.{u} S)).curvedDuplex w) inclusion :=
  ExactStructure.isConflationExact_ι isExtensionClosed_isProjective

/-- An inflation in the finite-projective subcategory is precisely an ambient componentwise
split inflation. Its cokernel remains finite projective. -/
@[simp] theorem splitExact_isInflation_iff {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (splitExact S w).IsInflation f ↔
      ((ExactStructure.split (FGModuleCat.{u} S)).curvedDuplex w).IsInflation f.hom := by
  refine ⟨isConflationExact_inclusion.map_isInflation, fun hf => ?_⟩
  obtain ⟨Z, p, hzero, hT⟩ := (ConflationClass.isInflation_iff _ _).mp hf
  let Z' : MatrixFactorization S w :=
    ⟨Z, (isProjective_outer_of_conflation hT Y.property).2⟩
  refine (ConflationClass.isInflation_iff _ _).mpr
    ⟨Z', ObjectProperty.homMk p, ObjectProperty.hom_ext _ hzero, ?_⟩
  rw [splitExact, ExactStructure.fullSubcategory_conflation_iff]
  exact hT

/-- A deflation in the finite-projective subcategory is precisely an ambient componentwise
split deflation. Its kernel remains finite projective. -/
@[simp] theorem splitExact_isDeflation_iff {X Y : MatrixFactorization S w} (f : X ⟶ Y) :
    (splitExact S w).IsDeflation f ↔
      ((ExactStructure.split (FGModuleCat.{u} S)).curvedDuplex w).IsDeflation f.hom := by
  refine ⟨isConflationExact_inclusion.map_isDeflation, fun hf => ?_⟩
  obtain ⟨Z, i, hzero, hT⟩ := (ConflationClass.isDeflation_iff _ _).mp hf
  let Z' : MatrixFactorization S w :=
    ⟨Z, (isProjective_outer_of_conflation hT X.property).1⟩
  refine (ConflationClass.isDeflation_iff _ _).mpr
    ⟨Z', ObjectProperty.homMk i, ObjectProperty.hom_ext _ hzero, ?_⟩
  rw [splitExact, ExactStructure.fullSubcategory_conflation_iff]
  exact hT

end TauCeti.MatrixFactorization
