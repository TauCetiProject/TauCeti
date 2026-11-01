/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.AuxiliaryMarks
public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.Diffeomorph.Sigma
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FixingSubgroup

/-!
# Automorphisms supported on one component, and unstable rational and elliptic components

A marked nodal curve is presented by its normalization components `X i`, its flag pairs and its
marks. A diffeomorphism of a single component `X i` which fixes every special point of `X i`
(every flag point and every mark lying on it, `Marking.specialPoints`) extends by the identity on
the other components to an automorphism of the marked curve fixing every label. These extensions
form an injective group homomorphism from the diffeomorphisms of `X i` fixing its special points
to the ordered automorphisms of the marked curve (`AuxiliaryAut.ofComponent`).

Consequently a component with infinitely many such diffeomorphisms makes the ordered automorphism
group infinite. This happens for a component diffeomorphic to the projective line carrying at most
two special points, where the Möbius dilations fixing those points give infinitely many
(`AuxiliaryAut.infinite_ordered_of_encard_specialPoints_le_two`). Contrapositively, when the
ordered automorphism group is finite, every component diffeomorphic to the projective line carries
at least three special points (`AuxiliaryAut.two_lt_encard_specialPoints`). Over `ℂ` this says that
in a marked nodal curve with finitely many automorphisms fixing every label, every component
biholomorphic to the Riemann sphere satisfies the stability condition `2 g_i - 2 + n_i > 0`.
Applying this to every genus-zero component requires identifying such a component with the
Riemann sphere, which is not done here.

Likewise a component without special points that is diffeomorphic to an infinite additive group
acting on itself by `C^n` translations, such as a complex torus `E / L` of positive dimension
(`Submodule.instInfiniteOrbitRelQuotient`), has infinitely many diffeomorphisms, namely the
translations, so the marked curve has infinitely many automorphisms fixing every label
(`AuxiliaryAut.infinite_ordered_of_specialPoints_eq_empty`). Contrapositively, when the ordered
automorphism group is finite, every component diffeomorphic to such a group carries a special point
(`AuxiliaryAut.nonempty_specialPoints`). Over `ℂ` this is the stability condition
`2 g_i - 2 + n_i > 0` for a component biholomorphic to a complex torus `ℂ / Λ`, of genus one.

## Main definitions

* `NodalGluing.AuxiliaryAut.ofComponent`: the ordered automorphism extending a diffeomorphism of
  one component fixing its special points, as a group homomorphism.

## Main results

* `NodalGluing.AuxiliaryAut.ofComponent_injective`: the extension is injective.
* `NodalGluing.AuxiliaryAut.infinite_ordered_of_infinite_fixingSubgroup`: a component with
  infinitely many diffeomorphisms fixing its special points gives infinitely many ordered
  automorphisms.
* `NodalGluing.AuxiliaryAut.infinite_ordered_of_encard_specialPoints_le_two`: so does a component
  diffeomorphic to the projective line with at most two special points.
* `NodalGluing.AuxiliaryAut.two_lt_encard_specialPoints`: if the ordered automorphism group is
  finite, every component diffeomorphic to the projective line has at least three special points.
* `NodalGluing.AuxiliaryAut.infinite_ordered_of_specialPoints_eq_empty`: a component without
  special points diffeomorphic to an infinite group with `C^n` translations, such as a complex
  torus, gives infinitely many ordered automorphisms.
* `NodalGluing.AuxiliaryAut.nonempty_specialPoints`: if the ordered automorphism group is finite,
  every such component carries a special point.

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

variable (m) in
/-- The diffeomorphism of the normalization extending a diffeomorphism of the component `i` by the
identity on the other components. -/
private noncomputable def extend (i : ι) :
    Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i) →*
      (Σ i, X i) ≃ₘ^n⟮I, I⟯ Σ i, X i :=
  open scoped Classical in
  Diffeomorph.sigmaCongrRightHom.comp ((MonoidHom.mulSingle _ i).comp (Subgroup.subtype _))

private theorem extend_apply_mk_self (i : ι)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : X i) :
    extend m i φ ⟨i, x⟩ = ⟨i, (φ : X i ≃ₘ^n⟮I, I⟯ X i) x⟩ := by
  classical
  simp [extend, Pi.mulSingle_eq_same]

private theorem extend_apply_mk_of_ne {i j : ι} (hj : j ≠ i)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : X j) :
    extend m i φ ⟨j, x⟩ = ⟨j, x⟩ := by
  classical
  simp [extend, Pi.mulSingle_eq_of_ne hj]

/-- The extension fixes every flag point and every mark. -/
private theorem extend_apply_of_mem (i : ι)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) {x : Σ i, X i}
    (hx : x ∈ flagPointSet d ∪ range m.point) : extend m i φ x = x := by
  obtain ⟨j, y⟩ := x
  by_cases hj : j = i
  · subst hj
    rw [extend_apply_mk_self,
      Diffeomorph.apply_eq_of_mem_fixingSubgroup φ.2 (Marking.mem_specialPoints_iff.mpr hx)]
  · exact extend_apply_mk_of_ne hj φ y

/-- The ordered automorphism with underlying map `extend m i φ`. -/
private noncomputable def toOrdered (i : ι)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) : ordered I n m :=
  ⟨{ toIso := ⟨extend m i φ, flagRel_apply_iff_of_forall_apply_eq _
        fun _ hx ↦ extend_apply_of_mem i φ (Or.inl hx)⟩
     perm := 1
     apply_inl' _ := extend_apply_of_mem i φ (Or.inr (mem_range_self _))
     apply_inr' _ := extend_apply_of_mem i φ (Or.inr (mem_range_self _)) },
    (mem_ordered_iff _).mpr rfl⟩

private theorem toOrdered_apply (i : ι)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : Σ i, X i) :
    (toOrdered i φ : AuxiliaryAut I n m) x = extend m i φ x :=
  (rfl)

/-- **Automorphisms supported on one component.** A diffeomorphism of the component `i` fixing
every special point of `i` (`Marking.specialPoints`), extended by the identity on the other
components, is an automorphism of the marked curve fixing every label. The extension is a group
homomorphism into the ordered automorphisms. -/
noncomputable def ofComponent (i : ι) :
    Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i) →* ordered I n m where
  toFun := toOrdered i
  map_one' := Subtype.ext <| AuxiliaryIso.ext fun x ↦ by simp [toOrdered_apply, one_def]
  map_mul' φ ψ := Subtype.ext <| AuxiliaryIso.ext fun x ↦ by simp [toOrdered_apply]

/-- On the component `i`, the extension acts by the given diffeomorphism. -/
@[simp]
theorem ofComponent_apply_mk_self (i : ι)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : X i) :
    (ofComponent i φ : AuxiliaryAut I n m) ⟨i, x⟩ = ⟨i, (φ : X i ≃ₘ^n⟮I, I⟯ X i) x⟩ :=
  (toOrdered_apply i φ _).trans (extend_apply_mk_self i φ x)

/-- Off the component `i`, the extension is the identity. -/
@[simp]
theorem ofComponent_apply_mk_of_ne {i j : ι} (hj : j ≠ i)
    (φ : Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) (x : X j) :
    (ofComponent i φ : AuxiliaryAut I n m) ⟨j, x⟩ = ⟨j, x⟩ :=
  (toOrdered_apply i φ _).trans (extend_apply_mk_of_ne hj φ x)

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

/-- **An unstable rational component.** If the component `i` is diffeomorphic to the projective
line `OnePoint 𝕜` and carries at most two special points, the marked curve has infinitely many
automorphisms fixing every label: Möbius transformations fixing those points act on the
component. -/
theorem infinite_ordered_of_encard_specialPoints_le_two [ProperSpace 𝕜] (i : ι)
    (e : X i ≃ₘ^n⟮I, 𝓘(𝕜)⟯ OnePoint 𝕜) (h : (m.specialPoints i).encard ≤ 2) :
    Infinite (ordered I n m) :=
  have := e.infinite_fixingSubgroup_of_encard_le_two h
  infinite_ordered_of_infinite_fixingSubgroup i

/-- **Projective-line components of a curve with finite automorphism group are stable.** If
the marked curve has finitely many automorphisms fixing every label, every component diffeomorphic
to the projective line carries at least three special points. -/
theorem two_lt_encard_specialPoints [ProperSpace 𝕜] [Finite (ordered I n m)] (i : ι)
    (e : X i ≃ₘ^n⟮I, 𝓘(𝕜)⟯ OnePoint 𝕜) : 2 < (m.specialPoints i).encard :=
  lt_of_not_ge fun h ↦ not_finite_iff_infinite.mpr
    (infinite_ordered_of_encard_specialPoints_le_two i e h) ‹_›

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {G : Type*} [AddGroup G] [TopologicalSpace G] [ChartedSpace H' G]
  [ContMDiffConstVAdd I' n G G] [Infinite G]

/-- **An unstable elliptic component.** If the component `i` carries no special points and is
diffeomorphic to an infinite additive group `G` whose translations are `C^n`, such as a complex
torus `E / L` of positive dimension, the marked curve has infinitely many automorphisms fixing
every label: the translations of `G` act on the component. -/
theorem infinite_ordered_of_specialPoints_eq_empty (i : ι) (e : X i ≃ₘ^n⟮I, I'⟯ G)
    (h : m.specialPoints i = ∅) : Infinite (ordered I n m) := by
  have : Infinite (X i ≃ₘ^n⟮I, I⟯ X i) :=
    (Diffeomorph.diffCongr e).toEquiv.infinite_iff.mpr
      (Diffeomorph.infinite_of_faithfulVAdd (G := G))
  have : Infinite (Diffeomorph.fixingSubgroup (I := I) (n := n) (m.specialPoints i)) := by
    rw [h, Diffeomorph.fixingSubgroup_empty]
    exact Subgroup.topEquiv.toEquiv.infinite_iff.mpr ‹_›
  exact infinite_ordered_of_infinite_fixingSubgroup i

/-- **Elliptic components of a curve with finite automorphism group are stable.** If the marked
curve has finitely many automorphisms fixing every label, every component diffeomorphic to an
infinite additive group with `C^n` translations, such as a complex torus `E / L` of positive
dimension, carries a special point. -/
theorem nonempty_specialPoints [Finite (ordered I n m)] (i : ι) (e : X i ≃ₘ^n⟮I, I'⟯ G) :
    (m.specialPoints i).Nonempty :=
  nonempty_iff_ne_empty.mpr fun h ↦ not_finite_iff_infinite.mpr
    (infinite_ordered_of_specialPoints_eq_empty i e h) ‹_›

end AuxiliaryAut

end NodalGluing

end TauCeti
