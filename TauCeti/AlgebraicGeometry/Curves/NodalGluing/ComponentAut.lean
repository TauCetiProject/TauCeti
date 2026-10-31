/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.AuxiliaryMarks
public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.Sigma
import Mathlib.GroupTheory.Index

/-!
# Componentwise automorphisms and finiteness of the automorphism group

A marked nodal curve is presented by its normalization components `X i`, its flag pairs and its
marks. A family of diffeomorphisms of the components, each fixing the special points of its
component (`Marking.specialPoints`: the flag points and marks lying on it), acts on the
normalization componentwise, and this is an automorphism of the marked curve fixing every label.
These automorphisms form an injective group homomorphism `AuxiliaryAut.ofComponents` from the
product of the groups of diffeomorphisms of the components fixing their special points to the
ordered automorphisms of the marked curve. Its image consists exactly of the ordered automorphisms
which carry every component to itself and fix every flag point
(`AuxiliaryAut.mem_range_ofComponents_iff`).

When there are finitely many components, each connected, and finitely many flags, an ordered
automorphism acts on the finite sets of components and branches, and the automorphisms acting
trivially on both are the componentwise ones. Hence the ordered automorphism group is finite
exactly when every component has finitely many diffeomorphisms fixing its special points
(`AuxiliaryAut.finite_ordered_iff`). This reduces the finiteness of the automorphism group of a
marked nodal curve to the corresponding question for each normalized component with its special
points. Over `ℂ`, by the classification of smooth marked curves (not proved here), a component of
genus `g_i` with `n_i` special points has finitely many automorphisms fixing them exactly when
`2 g_i - 2 + n_i > 0`. Some of the unstable cases, giving infinitely many automorphisms, are
treated in `TauCeti.AlgebraicGeometry.Curves.NodalGluing.UnstableComponent`.

## Main definitions

* `NodalGluing.AuxiliaryAut.ofComponents`: the ordered automorphism acting componentwise by a
  family of diffeomorphisms of the components fixing their special points, as a group
  homomorphism.

## Main results

* `NodalGluing.AuxiliaryAut.ofComponents_injective`: the componentwise action is injective.
* `NodalGluing.AuxiliaryAut.mem_range_ofComponents_iff`: an ordered automorphism is componentwise
  exactly when it carries every component to itself and fixes every flag point.
* `NodalGluing.AuxiliaryAut.finite_ordered`, `NodalGluing.AuxiliaryAut.finite_ordered_iff`: with
  finitely many components, each connected, and finitely many flags, the ordered automorphism group
  is finite exactly when every component has finitely many diffeomorphisms fixing its special
  points.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, §3, for stable marked nodal curves and the finiteness of
  their automorphism groups.
* Enrico Arbarello, Maurizio Cornalba, Phillip A. Griffiths, *Geometry of Algebraic Curves,
  Volume II*, Chapter X, §3, for stability of pointed nodal curves.
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

/-- **The componentwise automorphisms.** An ordered automorphism acts componentwise, by
diffeomorphisms of the components fixing their special points, exactly when it carries every
component to itself and fixes every flag point. -/
theorem mem_range_ofComponents_iff {g : ordered I n m} :
    g ∈ (ofComponents I n m).range ↔
      (∀ x, ((g : AuxiliaryAut I n m) x).1 = x.1) ∧
        ∀ x ∈ flagPointSet d, (g : AuxiliaryAut I n m) x = x := by
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨fun x ↦ by rw [ofComponents_apply],
      fun x hx ↦ (toOrdered_apply φ x).trans (sigmaCongrRight_apply_of_mem φ (Or.inl hx))⟩
  · rintro ⟨hfst, hflag⟩
    obtain ⟨e, he⟩ := Diffeomorph.exists_sigmaCongrRight_eq_iff.mpr hfst
    -- `g` fixes every special point: the flag points by hypothesis, the marks as it is ordered.
    have hfix (x : Σ i, X i) (hx : x ∈ flagPointSet d ∪ range m.point) :
        (g : AuxiliaryAut I n m) x = x := by
      rcases hx with hx | ⟨l, rfl⟩
      · exact hflag x hx
      · exact (mem_ordered_iff_forall _).mp g.2 l
    have hφ (i : ι) : e i ∈ Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i) :=
      Diffeomorph.mem_fixingSubgroup_of_forall fun y hy ↦ sigma_mk_injective (i := i) <| by
        have := DFunLike.congr_fun he ⟨i, y⟩
        rw [Diffeomorph.sigmaCongrRight_apply] at this
        rw [this]
        exact hfix _ (Marking.mem_specialPoints_iff.mp hy)
    refine ⟨fun i ↦ ⟨e i, hφ i⟩, Subtype.ext <| AuxiliaryIso.ext fun x ↦ ?_⟩
    rw [ofComponents_apply]
    have := DFunLike.congr_fun he x
    rwa [Diffeomorph.sigmaCongrRight_apply] at this

/-- **Finiteness of the ordered automorphism group from its components.** For a marked nodal curve
with finitely many components, each connected, and finitely many flags, if every component has
finitely many diffeomorphisms fixing its special points, the marked curve has finitely many
automorphisms fixing every label. -/
theorem finite_ordered [Finite ι] [Finite Flag] [∀ i, ConnectedSpace (X i)]
    [∀ i, Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i))] :
    Finite (ordered I n m) := by
  -- The action of the ordered automorphisms on the components and the branches.
  let φ : ordered I n m →* Equiv.Perm ι × Equiv.Perm (Flag × Bool) :=
    (Aut.vertexPerm.prod Aut.branchPerm).comp (toAut.comp (ordered I n m).subtype)
  rw [φ.finite_iff_finite_ker_range]
  refine ⟨((Set.finite_range (ofComponents I n m)).subset fun g hg ↦ ?_).to_subtype,
    inferInstance⟩
  -- An automorphism acting trivially on components and branches is componentwise.
  have hg : (g : AuxiliaryAut I n m).toIso.vertexEquiv = 1 ∧
      (g : AuxiliaryAut I n m).toIso.branchEquiv = 1 := by
    simpa [φ, Prod.ext_iff] using hg
  refine mem_range_ofComponents_iff.mpr ⟨fun x ↦ ?_, fun x hx ↦ ?_⟩
  · rw [← AuxiliaryIso.coe_toIso, Iso.fst_apply, hg.1, Equiv.Perm.one_apply]
  · rw [flagPointSet_eq_range] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [← AuxiliaryIso.coe_toIso, ← Iso.flagPoint_branchEquiv, hg.2, Equiv.Perm.one_apply]

/-- **Finiteness of the ordered automorphism group is decided componentwise.** For a marked nodal
curve with finitely many components, each connected, and finitely many flags, the automorphisms
fixing every label form a finite group exactly when every component has finitely many
diffeomorphisms fixing its special points. -/
theorem finite_ordered_iff [Finite ι] [Finite Flag] [∀ i, ConnectedSpace (X i)] :
    Finite (ordered I n m) ↔
      ∀ i, Finite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) := by
  classical
  refine ⟨fun _ i ↦ Finite.of_injective (fun φ ↦ ofComponents I n m (Pi.mulSingle i φ))
    (ofComponents_injective.comp (Pi.mulSingle_injective i)), fun _ ↦ finite_ordered⟩

end AuxiliaryAut

end NodalGluing

end TauCeti
