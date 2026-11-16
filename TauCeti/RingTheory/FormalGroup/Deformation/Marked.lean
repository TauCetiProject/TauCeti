/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Deformation.Basic
import TauCeti.RingTheory.PowerSeries.Coordinate.Lifting

/-!
# Marked special fibres of formal group deformations

A marked lift consists of a commutative formal group law over `A` and an isomorphism
from its reduction along `π : A →+* k` to a fixed law `F₀`. We encode the marking by
its formal coordinate, with the equation that transporting the reduced law gives `F₀`.
Changing coordinates over `A` also changes the marking by the inverse reduced coordinate.
The resulting orbit set is `MarkedFormalGroupDeformation π F₀`.

If coordinates lift along `π`, every marked deformation has a representative whose
special fibre equals `F₀` and whose marking is the identity. The equivalence
`FormalGroupDeformation.markedEquiv` identifies the fixed-special-fibre and marked
conventions, naturally under coefficient extension. In particular it applies to
surjective local coefficient maps, including residue maps. No completeness or height
hypothesis is needed for this comparison.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups*,
  Bull. Soc. Math. France 94 (1966).
-/

public section

noncomputable section

namespace TauCeti

variable {A B C k : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing k]

/-- A commutative lift with a specified special-fibre isomorphism to `F₀`, encoded by
its coordinate. The marking is directed from the reduced law to `F₀`. -/
@[ext]
structure MarkedFormalGroupLift (π : A →+* k) (F₀ : FormalGroup k) where
  /-- The law before reduction. -/
  formalGroup : FormalGroup A
  /-- The lifted law is commutative. -/
  isComm : formalGroup.IsComm
  /-- The coordinate of the special-fibre marking. -/
  marking : FormalCoordinate k
  /-- The marking transports the special fibre to the specified law. -/
  smul_map_eq : marking • formalGroup.map π = F₀

attribute [instance] MarkedFormalGroupLift.isComm

namespace MarkedFormalGroupLift

variable {π : A →+* k} {ρ : B →+* k} {τ : C →+* k} {F₀ : FormalGroup k}

/-- The special-fibre marking as a bundled formal group isomorphism. -/
def markingIso (F : MarkedFormalGroupLift π F₀) :
    FormalGroupIso (F.formalGroup.map π) F₀ :=
  ( { toPowerSeries := F.marking.toPowerSeries
      zero_constantCoeff := F.marking.constantCoeff_toPowerSeries
      hom := by
        simpa only [FormalGroup.smulIso_toHom_toPowerSeries, F.smul_map_eq] using
          (FormalGroup.smulIso F.marking (F.formalGroup.map π)).toHom.hom } :
    FormalGroupHom (F.formalGroup.map π) F₀).toIso F.marking.isUnit_coeff_one

/-- The marking isomorphism has exactly the specified coordinate. -/
@[simp]
theorem markingIso_toHom_toPowerSeries (F : MarkedFormalGroupLift π F₀) :
    F.markingIso.toHom.toPowerSeries = F.marking.toPowerSeries := by
  simp [markingIso]

/-- Every bundled special-fibre isomorphism determines a marked lift. -/
def ofIso {F : FormalGroup A} [F.IsComm] (e : FormalGroupIso (F.map π) F₀) :
    MarkedFormalGroupLift π F₀ where
  formalGroup := F
  isComm := inferInstance
  marking :=
    { toPowerSeries := e.toHom.toPowerSeries
      constantCoeff_toPowerSeries := e.toHom.zero_constantCoeff
      isUnit_coeff_one := e.isUnit_coeff_one }
  smul_map_eq := e.toHom.smul_eq rfl

/-- Encoding a bundled marking does not change the lifted law. -/
@[simp]
theorem formalGroup_ofIso {F : FormalGroup A} [F.IsComm]
    (e : FormalGroupIso (F.map π) F₀) : (ofIso e).formalGroup = F := (rfl)

/-- Encoding a bundled marking retains its forward coordinate. -/
@[simp]
theorem marking_ofIso_toPowerSeries {F : FormalGroup A} [F.IsComm]
    (e : FormalGroupIso (F.map π) F₀) :
    (ofIso e).marking.toPowerSeries = e.toHom.toPowerSeries := (rfl)

/-- Decoding an encoded bundled marking recovers the original isomorphism. -/
@[simp]
theorem markingIso_ofIso {F : FormalGroup A} [F.IsComm]
    (e : FormalGroupIso (F.map π) F₀) :
    (ofIso e).markingIso = (formalGroup_ofIso e).symm ▸ e := by
  unfold ofIso
  apply FormalGroupIso.ext
  apply FormalGroupHom.ext
  simp

/-- A marked lift is recovered from its law and its bundled marking. -/
@[simp]
theorem ofIso_markingIso (F : MarkedFormalGroupLift π F₀) : ofIso F.markingIso = F := by
  apply MarkedFormalGroupLift.ext (formalGroup_ofIso _)
  apply FormalCoordinate.ext
  simp

/-- Change coordinates on the lifted law and precompose the marking with the inverse
reduced coordinate. Thus the marked special fibre, not merely its isomorphism class, is retained. -/
instance : SMul (FormalCoordinate A) (MarkedFormalGroupLift π F₀) where
  smul φ F :=
    { formalGroup := φ • F.formalGroup
      isComm := inferInstance
      marking := F.marking * (FormalCoordinate.map π φ)⁻¹
      smul_map_eq := by
        rw [FormalGroup.map_smul, mul_smul, inv_smul_smul, F.smul_map_eq] }

/-- Change of coordinates acts on the underlying law. -/
@[simp]
theorem formalGroup_smul (φ : FormalCoordinate A) (F : MarkedFormalGroupLift π F₀) :
    (φ • F).formalGroup = φ • F.formalGroup := (rfl)

/-- The marking transforms contravariantly in the reduced coordinate. -/
@[simp]
theorem marking_smul (φ : FormalCoordinate A) (F : MarkedFormalGroupLift π F₀) :
    (φ • F).marking = F.marking * (FormalCoordinate.map π φ)⁻¹ := (rfl)

/-- Changes of coordinates act on marked lifts, retaining the specified special fibre. -/
instance : MulAction (FormalCoordinate A) (MarkedFormalGroupLift π F₀) where
  one_smul F := MarkedFormalGroupLift.ext (one_smul _ F.formalGroup) (by simp)
  mul_smul φ ψ F := MarkedFormalGroupLift.ext (mul_smul φ ψ F.formalGroup)
    (by simp [mul_assoc])

/-- Extend coefficients without changing the specified marking over `k`. -/
def map (F : MarkedFormalGroupLift π F₀) (f : A →+* B) (hf : ρ.comp f = π) :
    MarkedFormalGroupLift ρ F₀ where
  formalGroup := F.formalGroup.map f
  isComm := inferInstance
  marking := F.marking
  smul_map_eq := by rw [FormalGroup.map_comp, hf, F.smul_map_eq]

/-- Coefficient extension acts on the lifted law. -/
@[simp]
theorem formalGroup_map (F : MarkedFormalGroupLift π F₀) (f : A →+* B)
    (hf : ρ.comp f = π) : (F.map f hf).formalGroup = F.formalGroup.map f := (rfl)

/-- Coefficient extension leaves the special-fibre marking unchanged. -/
@[simp]
theorem marking_map (F : MarkedFormalGroupLift π F₀) (f : A →+* B)
    (hf : ρ.comp f = π) : (F.map f hf).marking = F.marking := (rfl)

/-- Coefficient extension commutes with changes of coordinates and their markings. -/
@[simp]
theorem map_smul (φ : FormalCoordinate A) (F : MarkedFormalGroupLift π F₀)
    (f : A →+* B) (hf : ρ.comp f = π) :
    (φ • F).map f hf = FormalCoordinate.map f φ • F.map f hf := by
  apply MarkedFormalGroupLift.ext
  · exact FormalGroup.map_smul f φ F.formalGroup
  · simp [← FormalCoordinate.map_comp, hf]

/-- Identity coefficient extension fixes a marked lift. -/
@[simp]
theorem map_id (F : MarkedFormalGroupLift π F₀) (h : π.comp (RingHom.id A) = π) :
    F.map (RingHom.id A) h = F := by ext <;> simp

/-- Successive coefficient extensions compose. -/
@[simp]
theorem map_comp (F : MarkedFormalGroupLift π F₀) (f : A →+* B) (hf : ρ.comp f = π)
    (g : B →+* C) (hg : τ.comp g = ρ) :
    (F.map f hf).map g hg = F.map (g.comp f) (by rw [← RingHom.comp_assoc, hg, hf]) := by
  ext <;> simp

/-- A fixed-special-fibre lift has the identity marking. -/
def ofLift (F : FormalGroupLift π F₀) : MarkedFormalGroupLift π F₀ where
  formalGroup := F.formalGroup
  isComm := inferInstance
  marking := 1
  smul_map_eq := by rw [one_smul, F.map_eq]

/-- The identity-marked lift has the original underlying law. -/
@[simp]
theorem formalGroup_ofLift (F : FormalGroupLift π F₀) :
    (ofLift F).formalGroup = F.formalGroup := (rfl)

/-- The marking attached to a fixed-special-fibre lift is the identity. -/
@[simp]
theorem marking_ofLift (F : FormalGroupLift π F₀) : (ofLift F).marking = 1 := (rfl)

/-- The identity-marking inclusion intertwines the kernel action and the full action. -/
@[simp]
theorem ofLift_smul (φ : (FormalCoordinate.map π).ker) (F : FormalGroupLift π F₀) :
    ofLift (φ • F) = φ.val • ofLift F := by
  ext <;> simp [MonoidHom.mem_ker.mp φ.property]

/-- The identity-marking inclusion commutes with coefficient extension. -/
@[simp]
theorem ofLift_map (F : FormalGroupLift π F₀) (f : A →+* B) (hf : ρ.comp f = π) :
    ofLift (F.map f hf) = (ofLift F).map f hf := by ext <;> simp

end MarkedFormalGroupLift

/-- Marked lifts modulo all coordinate changes over `A`, each acting on the law and
precomposing the marking with the inverse reduced coordinate. -/
abbrev MarkedFormalGroupDeformation (π : A →+* k) (F₀ : FormalGroup k) :=
  MulAction.orbitRel.Quotient (FormalCoordinate A) (MarkedFormalGroupLift π F₀)

namespace MarkedFormalGroupDeformation

variable {π : A →+* k} {ρ : B →+* k} {τ : C →+* k} {F₀ : FormalGroup k}

/-- Two marked lifts give the same deformation precisely when a change of coordinates
intertwines their laws and their special-fibre markings. -/
theorem mk_eq_mk_iff (F G : MarkedFormalGroupLift π F₀) :
    (⟦F⟧ : MarkedFormalGroupDeformation π F₀) = ⟦G⟧ ↔
      ∃ φ : FormalCoordinate A, φ • F.formalGroup = G.formalGroup ∧
        G.marking * FormalCoordinate.map π φ = F.marking := by
  rw [eq_comm, Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, congrArg MarkedFormalGroupLift.formalGroup hφ, ?_⟩
    rw [← hφ, MarkedFormalGroupLift.marking_smul, inv_mul_cancel_right]
  · rintro ⟨φ, hF, hmark⟩
    refine ⟨φ, MarkedFormalGroupLift.ext hF ?_⟩
    simpa using (eq_mul_inv_iff_mul_eq.mpr hmark).symm

/-- Coefficient extension of marked deformation classes. -/
def map (f : A →+* B) (hf : ρ.comp f = π) :
    MarkedFormalGroupDeformation π F₀ → MarkedFormalGroupDeformation ρ F₀ :=
  Quotient.map (fun F => F.map f hf) fun F G h => by
    obtain ⟨φ, rfl⟩ := MulAction.mem_orbit_iff.mp h
    exact MulAction.mem_orbit_iff.mpr ⟨_, (MarkedFormalGroupLift.map_smul φ G f hf).symm⟩

/-- Coefficient extension on a representative is extension of its marked lift. -/
@[simp]
theorem map_mk (f : A →+* B) (hf : ρ.comp f = π) (F : MarkedFormalGroupLift π F₀) :
    map f hf ⟦F⟧ = ⟦F.map f hf⟧ := (rfl)

/-- Identity coefficient extension fixes a marked deformation class. -/
@[simp]
theorem map_id (h : π.comp (RingHom.id A) = π) (x : MarkedFormalGroupDeformation π F₀) :
    map (RingHom.id A) h x = x := by
  exact Quotient.inductionOn x fun F => congrArg Quotient.mk'' (F.map_id h)

/-- Successive coefficient extensions of marked classes compose. -/
@[simp]
theorem map_comp (f : A →+* B) (hf : ρ.comp f = π) (g : B →+* C)
    (hg : τ.comp g = ρ) (x : MarkedFormalGroupDeformation π F₀) :
    map g hg (map f hf x) = map (g.comp f) (by rw [← RingHom.comp_assoc, hg, hf]) x := by
  exact Quotient.inductionOn x fun F => congrArg Quotient.mk'' (F.map_comp f hf g hg)

end MarkedFormalGroupDeformation

namespace FormalGroupDeformation

variable {π : A →+* k} {ρ : B →+* k} {F₀ : FormalGroup k}

/-- Regard a fixed-special-fibre deformation as a marked one with identity marking. -/
def toMarked : FormalGroupDeformation π F₀ → MarkedFormalGroupDeformation π F₀ :=
  Quotient.map MarkedFormalGroupLift.ofLift fun F G h => by
    obtain ⟨φ, rfl⟩ := MulAction.mem_orbit_iff.mp h
    exact MulAction.mem_orbit_iff.mpr ⟨φ.val, (MarkedFormalGroupLift.ofLift_smul φ G).symm⟩

/-- The comparison sends a lift to its identity-marked class. -/
@[simp]
theorem toMarked_mk (F : FormalGroupLift π F₀) :
    toMarked (⟦F⟧ : FormalGroupDeformation π F₀) = ⟦MarkedFormalGroupLift.ofLift F⟧ := (rfl)

/-- Adding the identity marking does not identify any further deformation classes. -/
theorem toMarked_injective :
    Function.Injective (toMarked : FormalGroupDeformation π F₀ → _) := by
  intro x y
  induction x using Quotient.inductionOn with | _ F =>
  induction y using Quotient.inductionOn with | _ G =>
  intro h
  obtain ⟨φ, hφ, hm⟩ := (MarkedFormalGroupDeformation.mk_eq_mk_iff _ _).mp h
  apply (mk_eq_mk_iff F G).mpr
  exact ⟨φ, by simpa using hm, hφ⟩

/-- If special-fibre coordinates lift, every marked deformation admits an identity-marked
representative. The required lift changes the law as well as the marking. -/
theorem toMarked_surjective (hπ : Function.Surjective (FormalCoordinate.map π)) :
    Function.Surjective (toMarked : FormalGroupDeformation π F₀ → _) := by
  intro x
  induction x using Quotient.inductionOn with | _ F =>
  obtain ⟨φ, hφ⟩ := hπ F.marking
  let G : FormalGroupLift π F₀ :=
    { formalGroup := φ • F.formalGroup
      isComm := inferInstance
      map_eq := by rw [FormalGroup.map_smul, hφ, F.smul_map_eq] }
  refine ⟨⟦G⟧, (MarkedFormalGroupDeformation.mk_eq_mk_iff _ _).mpr ?_⟩
  refine ⟨φ⁻¹, ?_, ?_⟩
  · exact inv_smul_smul φ F.formalGroup
  · simp [hφ]

/-- Fixed-special-fibre and arbitrarily marked deformations agree when coefficients
and units lift. This includes surjective local coefficient maps. -/
def markedEquiv (hπ : Function.Surjective π)
    (hu : Function.Surjective (Units.map π.toMonoidHom)) :
    FormalGroupDeformation π F₀ ≃ MarkedFormalGroupDeformation π F₀ :=
  Equiv.ofBijective toMarked ⟨toMarked_injective,
    toMarked_surjective ((FormalCoordinate.map_surjective_iff π).mpr ⟨hπ, hu⟩)⟩

/-- The equivalence is the identity-marking comparison, independent of lift choices. -/
@[simp]
theorem markedEquiv_apply (hπ : Function.Surjective π)
    (hu : Function.Surjective (Units.map π.toMonoidHom)) (x : FormalGroupDeformation π F₀) :
    markedEquiv hπ hu x = toMarked x := (rfl)

/-- The identity-marking comparison is natural under coefficient extension. -/
theorem toMarked_map (f : A →+* B) (hf : ρ.comp f = π) (x : FormalGroupDeformation π F₀) :
    toMarked (map f hf x) = MarkedFormalGroupDeformation.map f hf (toMarked x) := by
  induction x using Quotient.inductionOn with | _ F =>
  simp only [map_mk, toMarked_mk, MarkedFormalGroupDeformation.map_mk]
  exact congrArg Quotient.mk'' (MarkedFormalGroupLift.ofLift_map F f hf)

end FormalGroupDeformation

end TauCeti
