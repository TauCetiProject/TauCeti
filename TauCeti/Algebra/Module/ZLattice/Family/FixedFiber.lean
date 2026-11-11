/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Stabilizer
public import TauCeti.Topology.Algebra.GroupAction.Quotient

/-!
# Quotients of fixed fibres of a torus family

An affine action on a period-lattice family restricts to an action on the torus over any
fixed point of the base. Its linear and translation parts are the ones computed in
`TauCeti.Algebra.Module.ZLattice.Family.Stabilizer`. The inclusion of that torus is equivariant,
so its orbit space maps canonically and injectively to the orbit space of the total family.
For continuous periods and a continuous action on the total family, this map is a topological
embedding. Its image consists exactly of the orbits over the chosen fixed base point.

In particular, for a cyclic action over a rotated disc this identifies the quotient of the
central torus with the image of the central fibre in the total quotient. These are statements
about the standard orbit spaces and their quotient topologies; they require neither a lattice
basis nor a vector-space lift of the translation section. No manifold structure on the image
is asserted here.

## References

* W. P. Barth, K. Hulek, C. A. M. Peters, A. Van de Ven, *Compact Complex Surfaces*, second
  edition, Springer (2004), Chapter V, section *Logarithmic transformations*.
-/

public section

namespace TauCeti

variable {Y Λ E Γ : Type*} [AddCommGroup Λ] [AddCommGroup E] [Group Γ] [MulAction Γ Y]
  (R : Γ → Y → E →+ E)
  (hone : ∀ (y : Y) (v : E), R 1 y v = v)
  (hmul : ∀ (g h : Γ) (y : Y) (v : E), R (g * h) y v = R g (h • y) (R h y v))
  (P : Y → Λ →ₗ[ℤ] E) (ρ : Representation ℤ Γ Λ)
  (hP : ∀ (g : Γ) (y : Y) (l : Λ), P (g • y) (ρ g l) = R g y (P y l))
  (b : Γ → Y → letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E))
  (hb : ∀ (g : Γ) (y : Y), torusFamilyProjection P (b g y) = g • y)
  (hbone : ∀ y : Y, b 1 y = Quotient.mk _ (y, 0))
  (hbmul : ∀ (g h : Γ) (y : Y), b (g * h) y = torusFamilyAffineMap R P ρ hP b hb g (b h y))
  (y : Y) (hy : ∀ g : Γ, g • y = y)

/-- The affine action restricted to the torus over a fixed point of the base. -/
@[instance_reducible]
noncomputable def torusFamilyFixedFiberMulAction :
    MulAction Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) := by
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  letI : SMul Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :=
    ⟨fun g ↦ AddEquiv.affineEquiv (torusFamilyFiberLinearPart R hone hmul P ρ hP (hy g))
      (torusFamilyFiberTranslationPart P b hb (hy g))⟩
  exact Function.Injective.mulAction (torusFamilyFiberMap P y)
    (torusFamilyFiberMap_injective P y) fun g x ↦ by
      -- Expose the locally defined scalar action to compare it with the fibre formula.
      change torusFamilyFiberMap P y (AddEquiv.affineEquiv
        (torusFamilyFiberLinearPart R hone hmul P ρ hP (hy g))
        (torusFamilyFiberTranslationPart P b hb (hy g)) x) = g • torusFamilyFiberMap P y x
      simpa only [torusFamilyAffineMulAction_smul] using
        (torusFamilyAffineMap_fiberMap R hone hmul P ρ hP b hb (hy g) x).symm

/-- The restricted action has the computed affine linear and translation parts. -/
@[simp]
theorem torusFamilyFixedFiberMulAction_smul (g : Γ)
    (x : AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :
    letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
    g • x = AddEquiv.affineEquiv (torusFamilyFiberLinearPart R hone hmul P ρ hP (hy g))
      (torusFamilyFiberTranslationPart P b hb (hy g)) x := (rfl)

/-- The inclusion of a fixed fibre, as an equivariant map for the restricted affine action. -/
def torusFamilyFixedFiberHom :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
    MulActionHom (id : Γ → Γ) (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E)
      (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
  exact ⟨torusFamilyFiberMap P y, fun g x ↦ by
    rw [torusFamilyFixedFiberMulAction_smul, torusFamilyAffineMulAction_smul]
    exact (torusFamilyAffineMap_fiberMap R hone hmul P ρ hP b hb (hy g) x).symm⟩

/-- The equivariant inclusion is the usual fibre inclusion. -/
@[simp]
theorem torusFamilyFixedFiberHom_apply
    (x : AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :
    torusFamilyFixedFiberHom R hone hmul P ρ hP b hb hbone hbmul y hy x =
      torusFamilyFiberMap P y x := (rfl)

/-- Restricting a free affine action to a fixed fibre gives a free action on that torus. -/
theorem isCancelSMul_torusFamilyFixedFiberMulAction
    (hfree : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
      IsCancelSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E))) :
    letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
    IsCancelSMul Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
  have := hfree
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x hx
  apply IsCancelSMul.eq_one_of_smul (x := torusFamilyFiberMap P y x)
  have h := congrArg (torusFamilyFixedFiberHom R hone hmul P ρ hP b hb hbone hbmul y hy) hx
  simpa only [map_smulₛₗ, id_eq, torusFamilyFixedFiberHom_apply] using h

/-- The canonical map from the orbit space of a fixed fibre to the total orbit space. -/
noncomputable def torusFamilyFixedFiberQuotientMap :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
    MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) →
      MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  letI := periodAddAction P
  letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
  exact (torusFamilyFixedFiberHom R hone hmul P ρ hP b hb hbone hbmul y hy).orbitRelQuotientMap

/-- On fibre orbits, the map is the total orbit of the fibre inclusion. -/
@[simp]
theorem torusFamilyFixedFiberQuotientMap_mk
    (x : AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) :
    torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy
      (Quotient.mk _ x) = Quotient.mk _ (torusFamilyFiberMap P y x) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
  exact (torusFamilyFixedFiberHom R hone hmul P ρ hP b hb hbone hbmul y hy).orbitRelQuotientMap_mk x

/-- Distinct orbits in a fixed fibre remain distinct in the total orbit space. -/
theorem torusFamilyFixedFiberQuotientMap_injective :
    Function.Injective
      (torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
  exact MulActionHom.orbitRelQuotientMap_injective
    (torusFamilyFixedFiberHom R hone hmul P ρ hP b hb hbone hbmul y hy)
    (torusFamilyFiberMap_injective P y) Function.surjective_id

/-- The image is precisely the set of total orbits meeting the fibre over the fixed point. -/
theorem range_torusFamilyFixedFiberQuotientMap :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    Set.range (torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy) =
      Quotient.mk (MulAction.orbitRel Γ _) '' {z | torusFamilyProjection P z = y} := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
  rw [torusFamilyFixedFiberQuotientMap, MulActionHom.range_orbitRelQuotientMap]
  exact congrArg (fun s ↦ Quotient.mk (MulAction.orbitRel Γ _) '' s)
    (range_torusFamilyFiberMap P y)

/-- A total orbit lies in the fixed-fibre quotient exactly when its representative lies over
the fixed base point. Thus the image condition is independent of the representative. -/
@[simp]
theorem exists_torusFamilyFixedFiberQuotientMap_eq_mk_iff
    (z : letI := periodAddAction P; AddAction.orbitRel.Quotient Λ (Y × E)) :
    (∃ x, torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy x =
      Quotient.mk _ z) ↔ torusFamilyProjection P z = y := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  rw [← Set.mem_range, range_torusFamilyFixedFiberQuotientMap]
  constructor
  · rintro ⟨w, hw, heq⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.1 (Quotient.exact heq)
    have hp : g • torusFamilyProjection P z = torusFamilyProjection P w := by
      simpa only [torusFamilyAffineMulAction_smul, torusFamilyProjection_affineMap] using
        congrArg (torusFamilyProjection P) hg
    exact ((smul_eq_iff_eq_inv_smul g).1 (hp.trans hw)).trans (hy g⁻¹)
  · intro hz
    exact ⟨z, hz, rfl⟩

section Topology

variable [TopologicalSpace Y] [TopologicalSpace E] [ContinuousAdd E]
  (hcont : ∀ l, Continuous fun y ↦ P y l)
  (hact : letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    ContinuousConstSMul Γ (AddAction.orbitRel.Quotient Λ (Y × E)))

include hcont hact in
/-- The fixed-fibre quotient has its subspace topology in the total quotient. This needs no
freeness, finite group, full lattice, compactness or separation hypothesis. -/
theorem isEmbedding_torusFamilyFixedFiberQuotientMap :
    Topology.IsEmbedding
      (torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy) := by
  let _ := periodAddAction P
  let _ := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
  let _ := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
  have := hact
  exact MulActionHom.isEmbedding_orbitRelQuotientMap
    (torusFamilyFixedFiberHom R hone hmul P ρ hP b hb hbone hbmul y hy)
    (isEmbedding_torusFamilyFiberMap P y hcont) Function.surjective_id

/-- The quotient of the torus over a fixed point is canonically homeomorphic to its image
in the total quotient, with the inherited subspace topology. -/
noncomputable def torusFamilyFixedFiberQuotientHomeomorph :
    letI := periodAddAction P
    letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
    letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
    MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E) ≃ₜ
      (Quotient.mk (MulAction.orbitRel Γ _) '' {z | torusFamilyProjection P z = y}) :=
  (isEmbedding_torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy
    hcont hact).toHomeomorph.trans (Homeomorph.setCongr
      (range_torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy))

/-- The homeomorphism agrees with the canonical map on underlying orbit classes. -/
@[simp]
theorem coe_torusFamilyFixedFiberQuotientHomeomorph
    (x : letI := torusFamilyFixedFiberMulAction R hone hmul P ρ hP b hb hbone hbmul y hy
      MulAction.orbitRel.Quotient Γ (AddAction.orbitRel.Quotient (LinearMap.range (P y)) E)) :
    (torusFamilyFixedFiberQuotientHomeomorph R hone hmul P ρ hP b hb hbone hbmul y hy
      hcont hact x).1 =
      torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy x := (rfl)

/-- The inverse identification maps any point of the image to its preimage in the fibre quotient. -/
@[simp]
theorem torusFamilyFixedFiberQuotientMap_homeomorph_symm_apply
    (z : letI := periodAddAction P
      letI := torusFamilyAffineMulAction R hone hmul P ρ hP b hb hbone hbmul
      Quotient.mk (MulAction.orbitRel Γ _) '' {z | torusFamilyProjection P z = y}) :
    torusFamilyFixedFiberQuotientMap R hone hmul P ρ hP b hb hbone hbmul y hy
      ((torusFamilyFixedFiberQuotientHomeomorph R hone hmul P ρ hP b hb hbone hbmul y hy
        hcont hact).symm z) = z.1 := by
  simpa only [coe_torusFamilyFixedFiberQuotientHomeomorph] using
    congrArg Subtype.val
      ((torusFamilyFixedFiberQuotientHomeomorph R hone hmul P ρ hP b hb hbone hbmul y hy
        hcont hact).apply_symm_apply z)

end Topology

end TauCeti
