/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.AuxiliaryMarks
public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.Sigma

/-!
# Componentwise automorphisms of a marked nodal curve

A marked nodal curve is presented by its normalization components `X i`, its flag pairs and its
marks. A family of diffeomorphisms of the components, each fixing the special points of its
component (`Marking.specialPoints`: the flag points and marks lying on it), acts on the
normalization componentwise, and this is an automorphism of the marked curve fixing every label.
These automorphisms form an injective group homomorphism `AuxiliaryAut.ofComponents` from the
product of the groups of diffeomorphisms of the components fixing their special points to the
ordered automorphisms of the marked curve. Restricting to families supported on a single
component `i` gives the automorphisms extending a diffeomorphism of `X i` fixing its special points
by the identity on the other components (`AuxiliaryAut.ofComponent`), so a component with
infinitely many such diffeomorphisms makes the ordered automorphism group infinite
(`AuxiliaryAut.infinite_ordered_of_infinite_fixingSubgroup`).

The results here hold for any regularity `n` and need no compactness. They are used for the
componentwise finiteness criterion in
`TauCeti.AlgebraicGeometry.Curves.NodalGluing.FiniteAutomorphisms` and for the unstable rational
and elliptic components in `TauCeti.AlgebraicGeometry.Curves.NodalGluing.UnstableComponent`.

## Main definitions

* `NodalGluing.AuxiliaryAut.ofComponents`: the ordered automorphism acting componentwise by a
  family of diffeomorphisms of the components fixing their special points, as a group
  homomorphism.
* `NodalGluing.AuxiliaryAut.ofComponent`: its restriction to a diffeomorphism of a single component,
  extended by the identity on the other components.

## Main results

* `NodalGluing.AuxiliaryAut.ofComponents_injective`,
  `NodalGluing.AuxiliaryAut.ofComponent_injective`: the componentwise action and its
  single-component restriction are injective.
* `NodalGluing.AuxiliaryAut.infinite_ordered_of_infinite_fixingSubgroup`: a component with
  infinitely many diffeomorphisms fixing its special points gives infinitely many ordered
  automorphisms.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, §3, for automorphisms of marked nodal curves.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

namespace NodalGluing

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {ι Flag : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {d : FlagPairData ι Flag X} {N R : Type*} {m : Marking d (N ⊕ R)}

/-- A diffeomorphism of the normalization fixing every flag point carries flag pairs exactly to
flag pairs: it fixes both points of a flag pair, and a point it sends to a flag point is fixed. -/
private theorem flagRel_apply_iff_of_forall_apply_eq (F : (Σ i, X i) ≃ₘ^n⟮I, I⟯ Σ i, X i)
    (hF : ∀ x ∈ flagPointSet d, F x = x) (x y : Σ i, X i) :
    flagRel d (F x) (F y) ↔ flagRel d x y := by
  have hfix : ∀ z, F z ∈ flagPointSet d → F z = z := fun z hz ↦ F.injective (hF _ hz)
  have hmem : ∀ {a b}, flagRel d a b → a ∈ flagPointSet d ∧ b ∈ flagPointSet d := fun h ↦
    ⟨(mem_flagPointSet_iff_exists_flagRel d _).mpr ⟨_, h⟩,
      (mem_flagPointSet_iff_exists_flagRel d _).mpr ⟨_, flagRel_symm d h⟩⟩
  constructor
  · intro h
    rwa [hfix x (hmem h).1, hfix y (hmem h).2] at h
  · intro h
    rwa [hF x (hmem h).1, hF y (hmem h).2]

namespace AuxiliaryAut

/-- The componentwise diffeomorphism of the normalization fixes every flag point and every
mark. -/
private theorem sigmaCongrRight_apply_of_mem
    (φ : ∀ i, Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i))
    {x : Σ i, X i} (hx : x ∈ flagPointSet d ∪ range m.point) :
    Diffeomorph.sigmaCongrRight (fun i ↦ (φ i : X i ≃ₘ^n⟮I, I⟯ X i)) x = x := by
  obtain ⟨i, y⟩ := x
  rw [Diffeomorph.sigmaCongrRight_apply,
    Diffeomorph.apply_eq_of_mem_fixingSubgroup (φ i).2 (Marking.mem_specialPoints_iff.mpr hx)]

/-- The ordered automorphism acting componentwise by `φ`. -/
private noncomputable def toOrdered
    (φ : ∀ i, Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) :
    ordered I n m :=
  ⟨{ toIso := ⟨Diffeomorph.sigmaCongrRight fun i ↦ (φ i : X i ≃ₘ^n⟮I, I⟯ X i),
        flagRel_apply_iff_of_forall_apply_eq _
          fun _ hx ↦ sigmaCongrRight_apply_of_mem φ (Or.inl hx)⟩
     perm := 1
     apply_inl' _ := sigmaCongrRight_apply_of_mem φ (Or.inr (mem_range_self _))
     apply_inr' _ := sigmaCongrRight_apply_of_mem φ (Or.inr (mem_range_self _)) },
    (mem_ordered_iff _).mpr rfl⟩

private theorem toOrdered_apply
    (φ : ∀ i, Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : Σ i, X i) :
    (toOrdered φ : AuxiliaryAut I n m) x =
      Diffeomorph.sigmaCongrRight (fun i ↦ (φ i : X i ≃ₘ^n⟮I, I⟯ X i)) x :=
  (rfl)

variable (I n m) in
/-- **Componentwise automorphisms.** A family of diffeomorphisms of the components, each fixing
the special points of its component (`Marking.specialPoints`), acting componentwise on the
normalization, is an automorphism of the marked curve fixing every label. This is a group
homomorphism into the ordered automorphisms. -/
noncomputable def ofComponents :
    (∀ i, Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) →* ordered I n m where
  toFun := toOrdered
  map_one' := Subtype.ext <| AuxiliaryIso.ext fun x ↦ by simp [toOrdered_apply]
  map_mul' _ _ := Subtype.ext <| AuxiliaryIso.ext fun x ↦ by simp [toOrdered_apply]

/-- The componentwise automorphism acts on the component `i` by the diffeomorphism `φ i`. -/
@[simp]
theorem ofComponents_apply
    (φ : ∀ i, Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : Σ i, X i) :
    (ofComponents I n m φ : AuxiliaryAut I n m) x = ⟨x.1, (φ x.1 : X x.1 ≃ₘ^n⟮I, I⟯ X x.1) x.2⟩ :=
  (toOrdered_apply φ x).trans (Diffeomorph.sigmaCongrRight_apply _ x)

/-- A family of diffeomorphisms of the components is determined by the componentwise
automorphism. -/
theorem ofComponents_injective : Function.Injective (ofComponents I n m) := by
  intro φ ψ h
  funext i
  refine Subtype.ext <| Diffeomorph.ext fun x ↦ sigma_mk_injective (i := i) ?_
  have := congrArg (fun g : ordered I n m ↦ (g : AuxiliaryAut I n m) ⟨i, x⟩) h
  simpa only [ofComponents_apply] using this

/-- **Automorphisms supported on one component.** A diffeomorphism of the component `i` fixing
every special point of `i` (`Marking.specialPoints`), extended by the identity on the other
components, is an automorphism of the marked curve fixing every label. The extension is a group
homomorphism into the ordered automorphisms. -/
noncomputable def ofComponent (i : ι) :
    Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i) →* ordered I n m :=
  open scoped Classical in
  (ofComponents I n m).comp <| MonoidHom.mulSingle
    (fun j ↦ Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints j)) i

/-- On the component `i`, the extension acts by the given diffeomorphism. -/
@[simp]
theorem ofComponent_apply_mk_self (i : ι)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : X i) :
    (ofComponent i φ : AuxiliaryAut I n m) ⟨i, x⟩ = ⟨i, (φ : X i ≃ₘ^n⟮I, I⟯ X i) x⟩ := by
  classical
  simp [ofComponent, Pi.mulSingle_eq_same]

/-- Off the component `i`, the extension is the identity. -/
@[simp]
theorem ofComponent_apply_mk_of_ne {i j : ι} (hj : j ≠ i)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : X j) :
    (ofComponent i φ : AuxiliaryAut I n m) ⟨j, x⟩ = ⟨j, x⟩ := by
  classical
  simp [ofComponent, Pi.mulSingle_eq_of_ne hj]

/-- A diffeomorphism of a component is determined by the automorphism it extends to. -/
theorem ofComponent_injective (i : ι) :
    Function.Injective (ofComponent (I := I) (n := n) (m := m) i) := by
  intro φ ψ h
  refine Subtype.ext <| Diffeomorph.ext fun x ↦ sigma_mk_injective (i := i) ?_
  rw [← ofComponent_apply_mk_self, ← ofComponent_apply_mk_self, h]

/-- **Infinitely many automorphisms from one component.** If the component `i` has infinitely many
diffeomorphisms fixing its special points, the marked curve has infinitely many automorphisms
fixing every label. -/
theorem infinite_ordered_of_infinite_fixingSubgroup (i : ι)
    [Infinite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i))] :
    Infinite (ordered I n m) :=
  Infinite.of_injective _ (ofComponent_injective i)

end AuxiliaryAut

end NodalGluing

end TauCeti
