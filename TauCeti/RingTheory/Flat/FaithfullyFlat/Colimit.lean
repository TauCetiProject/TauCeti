/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.Algebra.Category.CommAlgCat.DirectLimit
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.Algebra.Category.AlgCat.FilteredColimits
import TauCeti.Algebra.Category.CommAlgCat.BaseChange
import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits
import TauCeti.RingTheory.Flat.Colimit

/-!
# Faithful flatness of filtered colimits of algebras

`Module.FaithfullyFlat.of_isColimit` shows that a small filtered colimit of faithfully flat
commutative algebras is faithfully flat. Flatness follows from `Module.Flat.of_isColimit`.
For each maximal ideal of the base, extension of scalars to the residue field preserves
the colimit, and `CommRingCat.FilteredColimits.nontrivial` gives a nonzero fibre.
`Module.FaithfullyFlat.directLimit` applies the result to `DirectLimit` of a directed
system of algebras.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

universe u

namespace Module.FaithfullyFlat

/-- The colimit of a small filtered diagram of faithfully flat commutative `R`-algebras is
faithfully flat over `R`. The empty diagram has colimit `R`. -/
theorem of_isColimit {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFilteredOrEmpty J]
    {F : J ⥤ CommAlgCat.{u} R} {c : Cocone F} (hc : IsColimit c)
    [∀ j, FaithfullyFlat R (F.obj j)] : FaithfullyFlat R c.pt := by
  cases isEmpty_or_nonempty J
  · have hinit : IsInitial c.pt := isColimitEquivIsInitialOfIsEmpty (CommAlgCat.{u} R) c hc
    let e := hinit.uniqueUpToIso (CommAlgCat.isInitialSelf (R := R))
    exact of_linearEquiv R R (CommAlgCat.algEquivOfIso e).toLinearEquiv
  have : IsFiltered J := ⟨⟩
  have hflat : Flat R c.pt := by
    let U := forget₂ (CommAlgCat.{u} R) (AlgCat.{u} R) ⋙
      forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)
    have (j : J) : Flat R ((F ⋙ U).obj j) := inferInstanceAs (Flat R (F.obj j))
    exact Module.Flat.of_isColimit (isColimitOfPreserves U hc)
  refine ⟨fun m hm ↦ ?_⟩
  have hfiber : Nontrivial ((R ⧸ m) ⊗[R] c.pt) := by
    have : m.IsMaximal := hm
    let E := CommAlgCat.extendScalars R (R ⧸ m) ⋙
      forget₂ (CommAlgCat.{u} (R ⧸ m)) CommRingCat.{u}
    have (j : J) : Nontrivial ((F ⋙ E).obj j) :=
      inferInstanceAs (Nontrivial ((R ⧸ m) ⊗[R] F.obj j))
    exact CommRingCat.FilteredColimits.nontrivial (isColimitOfPreserves E hc)
  have : Nontrivial (c.pt ⧸ (m • (⊤ : Submodule R c.pt))) :=
    (TensorProduct.quotTensorEquivQuotSMul c.pt m).toEquiv.symm.nontrivial
  exact mt Submodule.Quotient.subsingleton_iff.mpr (not_subsingleton _)

/-- The direct limit of a nonempty directed system of faithfully flat `R`-algebras
is faithfully flat over `R`. -/
theorem directLimit {R ι : Type u} [CommRing R] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
    (f : ∀ i j, i ≤ j → B i →ₐ[R] B j) [DirectedSystem B (f · · ·)]
    [∀ i, FaithfullyFlat R (B i)] : FaithfullyFlat R (_root_.DirectLimit B f) :=
  of_isColimit (CommAlgCat.directLimitIsColimit B f)

end Module.FaithfullyFlat
