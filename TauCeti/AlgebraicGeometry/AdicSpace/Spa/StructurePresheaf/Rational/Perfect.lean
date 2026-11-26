/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.SheafyRing
public import TauCeti.RingTheory.Perfectoid.RationalLocalization.CharP

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.StableUniform
import TauCeti.RingTheory.Perfect.Basic

/-!
# The structure sheaf of a perfect Tate ring

The adic structure presheaf of a perfect complete Hausdorff Tate ring of characteristic `p`
is a sheaf, by the stable uniformity criterion of Buzzard and Verberkmoes. Its sections over
any rational open form a perfect ring.
-/

public section

open CategoryTheory TopologicalSpace UniformSpace
open TauCeti.Huber TauCeti.Huber.PairOfDefinition

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [IsTopologicalRing A] [IsTateRing A] [CompleteSpace A] [T2Space A]
  {p : ℕ} [Fact p.Prime] [PerfectRing A p]

/-- A perfect complete Hausdorff Tate ring in which `p = 0` is sheafy. -/
theorem TauCeti.Huber.isSheafyRing_of_perfectRing (hp0 : (p : A) = 0) : IsSheafyRing A :=
  have := isStablyUniform_of_perfectRing hp0
  isSheafyRing_of_isStablyUniform

namespace TauCeti.ValuationSpectrum

/-- The sections on a rational open of the adic spectrum of a perfect complete Hausdorff Tate
ring in which `p = 0` form a perfect ring. -/
theorem perfectRing_presentationLimit_of_mem_spaRationalOpens (P : PairOfDefinition A)
    (hp0 : (p : A) = 0) {Aplus : Subring A}
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) {U : Opens (spa Aplus)}
    (hU : U ∈ spaRationalOpens Aplus) : PerfectRing (presentationLimit (P := P) Aplus U) p := by
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hU
  let S := Localization.Away s
  let d : Presentation P := ⟨T, s, P.hasDenominatorPower_of_isOpen_span T s S hT⟩
  let _ := P.locUniformSpace T s S d.hasDenominatorPower
  have _ := P.isUniformAddGroup_locUniformSpace T s S d.hasDenominatorPower
  have _ := P.isTopologicalRing_locUniformSpace T s S d.hasDenominatorPower
  let e := presentationLimitRationalIso Aplus hAplus d hT
  let f : presentationLimit (P := P) Aplus (spaBasicOpen Aplus T s) →+* Completion S :=
    (eqToHom (completionLocObj_obj P T s S d.hasDenominatorPower)).val.comp e.hom.hom.val
  have hf : Function.Bijective f := bijective_presentationLimitRationalIso_hom Aplus hAplus d hT
  have := P.perfectRing_completion_locTopology T s S d.hasDenominatorPower hp0
  exact (RingEquiv.ofBijective f hf).symm.toMulEquiv.perfectRing p

end TauCeti.ValuationSpectrum
