/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction
public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.SubgroupWeights
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import Mathlib.RingTheory.Flat.Equalizer
import TauCeti.LinearAlgebra.TensorProduct.Basic
import TauCeti.LinearAlgebra.TensorProduct.Intersection

/-!
# Invariants of normal closed subgroups

Let `H` be a commutative Hopf algebra and `M` an `H`-comodule. A point of the affine group
represented by `H` acts naturally on `M` itself when its value algebra is the base ring. For a
Hopf ideal `I`, this file defines the submodule fixed by the base-valued points of the closed
subgroup cut out by `I`.

When `I` is normal, its point subgroup is normal over every value algebra. The standard theorem
that the invariants of a normal subgroup form a subrepresentation therefore shows that this
fixed submodule is preserved by every ambient point. This is the pointwise algebraic-group input
to the direct proof that `GLₙ` is reductive: the fixed vectors of a normal unipotent subgroup in
the standard representation form an ambient subrepresentation.

The definition deliberately says `basePointFixedSubmodule`: without a point-separation
hypothesis, base-valued points need not detect scheme-theoretic invariants. The normality and
stability results require no reducedness, finite-type, or field hypotheses.

Over any field, `HopfIdeal.IsNormal.weightSpaceOneSubcomodule` instead constructs the
scheme-theoretic invariant representation, the subgroup's trivial-character weight space. A vector
is invariant exactly when its matrix coefficients lie in the coinvariants of `I`, the functions
invariant under right translation by the subgroup. For a normal subgroup these coinvariants are
also invariant under left translation, and this makes the invariant vectors ambient-stable. The
coaction on them then has coefficients in the coinvariants, the coordinate ring of the quotient
group. Neither group needs to be reduced or of finite type.

The group-representation step is Mathlib's `Representation.toInvariants`; this file adds the
Hopf-ideal and comodule interface around it rather than repeating the normal-subgroup conjugation
argument.

## Main declarations

* `TauCeti.HopfIdeal.basePointFixedSubmodule`: the vectors fixed by the base-valued points cut out
  by a Hopf ideal.
* `TauCeti.HopfIdeal.mem_basePointFixedSubmodule_iff_quotient_coact_eq_tmul_one`: geometric-point
  detection identifies the pointwise and scheme-theoretic fixed-vector conditions.
* `TauCeti.HopfIdeal.IsNormal.basePointFixedSubrepresentation`: Mathlib's representation on the
  invariants of the point subgroup cut out by a normal Hopf ideal.
* `TauCeti.HopfIdeal.IsNormal.basePointsRepresentation_mem_basePointFixedSubmodule`: the ambient
  base-point action preserves the base-point-fixed submodule.
* `TauCeti.HopfIdeal.IsNormal.endOfPoint_one_tmul_mem_basePointFixedSubmodule_baseChange`:
  pointwise
  stability in the scalar-extension form used to detect subcomodules.
* `TauCeti.HopfIdeal.mem_weightSpace_one_iff_coact_mem_range`: a vector is invariant under the
  closed subgroup exactly when its matrix coefficients are coinvariants.
* `TauCeti.HopfIdeal.IsNormal.weightSpaceOneSubcomodule`: the scheme-theoretic invariant
  representation of a normal subgroup, over any field.
* `TauCeti.HopfIdeal.IsNormal.weightSpaceOneLinearEquiv`: identifies the weight-space and
  subcomodule presentations of the invariant vectors.
* `TauCeti.HopfIdeal.IsNormal.coact_mem_range_lTensor_coinvariants`: its coaction has
  coefficients in the coordinate ring of the quotient group.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and I.6.
* T. A. Springer, *Linear Algebraic Groups*, §2.2.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open scoped TensorProduct

namespace TauCeti

open CategoryTheory WithConv

universe u v w x

noncomputable section

namespace HopfIdeal

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommGroup M] [Module R M] [Comodule R H M]

variable (M) in
/-- The submodule fixed by all base-valued points of the closed subgroup cut out by `I`. -/
def basePointFixedSubmodule (I : HopfIdeal R H) : Submodule R M :=
  Representation.invariants
    ((Comodule.basePointsRepresentation (R := R) (H := H) M).comp
      (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
        (CommAlgCat.of R R)).subtype)

/-- The base-point-fixed submodule as Mathlib's invariant submodule for the quotient point
subgroup. -/
theorem basePointFixedSubmodule_def (I : HopfIdeal R H) :
    I.basePointFixedSubmodule M =
      Representation.invariants
        ((Comodule.basePointsRepresentation (R := R) (H := H) M).comp
          (CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
            (CommAlgCat.of R R)).subtype) := by
  rfl

/-- Membership in the base-point-fixed submodule means being fixed by every base-valued point cut
out by the Hopf ideal. -/
@[simp]
theorem mem_basePointFixedSubmodule (I : HopfIdeal R H) (m : M) :
    m ∈ I.basePointFixedSubmodule M ↔
      ∀ n : CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
          (CommAlgCat.of R R),
        Comodule.basePointsRepresentation (R := R) (H := H) M
          (n : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) m = m := by
  rfl

/-- A vector fixed by the quotient coaction is fixed by every base-valued point of the closed
subgroup cut out by `I`. This direction requires no point-separation hypotheses. -/
theorem mem_basePointFixedSubmodule_of_quotient_coact_eq_tmul_one
    (I : HopfIdeal R H) (m : M)
    (hm : TensorProduct.map LinearMap.id
        (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of R H) I).hom.toLinearMap
        (Comodule.coact (R := R) (C := H) m) =
      m ⊗ₜ[R] (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of R H) I)) :
    m ∈ I.basePointFixedSubmodule M := by
  let A := _root_.CommHopfAlgCat.of R H
  let Q := CommHopfAlgCat.quotient A I
  let q : H →ₐc[R] Q := (CommHopfAlgCat.mkQuotient A I).hom
  let _ : Comodule R Q M := Comodule.Corestrict q.toCoalgHom
  have hm' : Comodule.coact (R := R) (C := Q) m = m ⊗ₜ[R] (1 : Q) := by
    simpa only [Comodule.corestrict_coact_apply] using hm
  rw [mem_basePointFixedSubmodule]
  intro n
  obtain ⟨g, hg⟩ := n.2
  have hfixed := Comodule.basePointsRepresentation_eq_of_coact_eq_tmul_one m hm' g
  have hinclude : BialgHom.mapDomain q g =
      CommHopfAlgCat.quotientPointsHom A I (CommAlgCat.of R R) g := by
    rw [CommHopfAlgCat.quotientPointsHom_apply, BialgHom.mapDomain_apply]
  have hq : BialgHom.mapDomain q g = n.1 := by
    exact hinclude.trans hg
  rw [Comodule.basePointsRepresentation_corestrict q g, hq] at hfixed
  exact hfixed

section GeometricDetection

variable {k : Type u} {A : Type v} {M : Type w}
variable [Field k] [CommRing A] [HopfAlgebra k A]
variable [AddCommGroup M] [Module k M] [Comodule k A M] [IsAlgClosed k]

/-- Over an algebraically closed field, if the quotient coordinate ring is reduced and of finite
type, base-point-fixed vectors are exactly the vectors fixed by the restricted coaction of the
closed subgroup scheme. -/
theorem mem_basePointFixedSubmodule_iff_quotient_coact_eq_tmul_one
    (I : HopfIdeal k A)
    [Algebra.FiniteType k
      (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I)]
    [IsReduced (CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I)]
    (m : M) :
    m ∈ I.basePointFixedSubmodule M ↔
      TensorProduct.map LinearMap.id
          (CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k A) I).hom.toLinearMap
          (Comodule.coact (R := k) (C := A) m) =
        m ⊗ₜ[k]
          (1 : CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k A) I) := by
  let H := _root_.CommHopfAlgCat.of k A
  let Q := CommHopfAlgCat.quotient H I
  let q : A →ₐc[k] Q := (CommHopfAlgCat.mkQuotient H I).hom
  let _ : Comodule k Q M := Comodule.Corestrict q.toCoalgHom
  have hinclude (g : HopfAlgebra.points (R := k) (H := Q) (CommAlgCat.of k k)) :
      BialgHom.mapDomain q g =
        CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) g := by
    rw [CommHopfAlgCat.quotientPointsHom_apply, BialgHom.mapDomain_apply]
  constructor
  · intro hm
    have hfixed : ∀ g : HopfAlgebra.points (R := k) (H := Q) (CommAlgCat.of k k),
        Comodule.basePointsRepresentation (R := k) (H := Q) M g m = m := by
      intro g
      let n := CommHopfAlgCat.quotientPointsHom H I (CommAlgCat.of k k) g
      have hn := (mem_basePointFixedSubmodule I m).mp hm
        ⟨n, CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H I
          (CommAlgCat.of k k) g⟩
      rw [Comodule.basePointsRepresentation_corestrict q g, hinclude]
      exact hn
    have hcoact :=
      (Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq m).2 hfixed
    simpa only [Comodule.corestrict_coact_apply] using hcoact
  · exact mem_basePointFixedSubmodule_of_quotient_coact_eq_tmul_one I m

end GeometricDetection

section Field

variable {k : Type u} {A : Type v} {V : Type w}
variable [Field k] [CommRing A] [HopfAlgebra k A]
variable [AddCommMonoid V] [Module k V] [Comodule k A V]
variable {I : HopfIdeal k A}

private theorem lTensor_coassoc_natural {Q : Type x} [AddCommMonoid Q] [Module k Q]
    (π : A →ₗ[k] Q) (v : V) :
    (π.lTensor A ∘ₗ Coalgebra.comul).lTensor V (Comodule.coact (R := k) (C := A) v) =
      TensorProduct.assoc k V A Q
        ((Comodule.coact (R := k) (C := A)).rTensor Q
          (π.lTensor V (Comodule.coact (R := k) (C := A) v))) := by
  rw [LinearMap.lTensor_comp_apply, ← Comodule.coassoc_apply]
  exact LinearMap.lTensor_assoc_rTensor_natural π (Comodule.coact (R := k) (C := A))
    (Comodule.coact (R := k) (C := A) v)

private theorem assoc_rTensor_coact_natural {Q : Type x} [AddCommMonoid Q] [Module k Q]
    (π : A →ₗ[k] Q) (v : V) :
    TensorProduct.assoc k V Q A
        ((π.lTensor V ∘ₗ Comodule.coact (R := k) (C := A)).rTensor A
          (Comodule.coact (R := k) (C := A) v)) =
      (π.rTensor A).lTensor V
        (Coalgebra.comul.lTensor V (Comodule.coact (R := k) (C := A) v)) := by
  rw [← Comodule.coassoc_apply]
  exact LinearMap.assoc_rTensor_lTensor_natural π (Comodule.coact (R := k) (C := A))
    (Comodule.coact (R := k) (C := A) v)

private theorem assoc_rTensor_coact_eq_lTensor_one_of_mem_range
    {Q : Type x} [AddCommMonoid Q] [Module k Q] [One Q] (B : Submodule k A) (π : A →ₗ[k] Q)
    {v : V} {x : V ⊗[k] B}
    (hx : B.subtype.lTensor V x = Comodule.coact (R := k) (C := A) v)
    (hleft : π.rTensor A ∘ₗ Coalgebra.comul ∘ₗ B.subtype =
      TensorProduct.mk k Q A 1 ∘ₗ B.subtype) :
    TensorProduct.assoc k V Q A
        ((π.lTensor V ∘ₗ Comodule.coact (R := k) (C := A)).rTensor A
          (Comodule.coact (R := k) (C := A) v)) =
      (TensorProduct.mk k Q A 1).lTensor V (Comodule.coact (R := k) (C := A) v) := by
  calc
    _ = (π.rTensor A).lTensor V
        (Coalgebra.comul.lTensor V (Comodule.coact (R := k) (C := A) v)) :=
      assoc_rTensor_coact_natural π v
    _ = (π.rTensor A ∘ₗ Coalgebra.comul).lTensor V
        (Comodule.coact (R := k) (C := A) v) := by
      rw [LinearMap.lTensor_comp_apply]
    _ = (π.rTensor A ∘ₗ Coalgebra.comul).lTensor V (B.subtype.lTensor V x) := by rw [hx]
    _ = ((π.rTensor A ∘ₗ Coalgebra.comul) ∘ₗ B.subtype).lTensor V x := by
      exact (LinearMap.lTensor_comp_apply V (f := B.subtype)
        (g := π.rTensor A ∘ₗ Coalgebra.comul) x).symm
    _ = (TensorProduct.mk k Q A 1 ∘ₗ B.subtype).lTensor V x := by
      rw [LinearMap.comp_assoc, hleft]
    _ = (TensorProduct.mk k Q A 1).lTensor V (B.subtype.lTensor V x) := by
      rw [LinearMap.lTensor_comp_apply]
    _ = _ := by rw [hx]

/-- **Invariant vectors have invariant matrix coefficients.** Over a field, a vector is fixed by
the closed subgroup cut out by `I` exactly when its coaction has coefficients in the coinvariants
of `I`, the functions invariant under right translation by that subgroup. -/
theorem mem_weightSpace_one_iff_coact_mem_range {v : V} :
    v ∈ I.weightSpace V 1 ↔
      Comodule.coact (R := k) (C := A) v ∈
        LinearMap.range ((Subalgebra.toSubmodule I.coinvariants).subtype.lTensor V) := by
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let Q := A ⧸ I.toIdeal
  set B := Subalgebra.toSubmodule I.coinvariants
  let π : A →ₗ[k] Q := (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap
  rw [mem_weightSpace, GroupLike.val_one]
  constructor
  · intro hv
    -- The coinvariants are the equalizer of `(id ⊗ π) ∘ Δ` and `· ⊗ 1`; flatness of `V` makes
    -- `V ⊗ B` the equalizer of the two maps after tensoring with `V`.
    let f : A →ₗ[k] A ⊗[k] Q := π.lTensor A ∘ₗ Coalgebra.comul
    let g : A →ₗ[k] A ⊗[k] Q := (TensorProduct.mk k A Q).flip 1
    have hmap (y : A ⊗[k] A) :
        Algebra.TensorProduct.map (AlgHom.id k A) (Ideal.Quotient.mkₐ k I.toIdeal) y =
          π.lTensor A y := by
      induction y with
      | tmul a b => simp [π]
      | add y z hy hz => simp [hy, hz]
    have hB : B = LinearMap.eqLocus f g := by
      ext x
      simp [B, mem_coinvariants_iff, hmap, f, g]
    have hf : f.lTensor V (Comodule.coact (R := k) (C := A) v) =
        TensorProduct.assoc k V A Q (Comodule.coact (R := k) (C := A) v ⊗ₜ[k] 1) := by
      have hv' : π.lTensor V (Comodule.coact (R := k) (C := A) v) = v ⊗ₜ[k] 1 := hv
      rw [lTensor_coassoc_natural, hv', LinearMap.rTensor_tmul]
    have hg (y : V ⊗[k] A) : g.lTensor V y = TensorProduct.assoc k V A Q (y ⊗ₜ[k] 1) := by
      induction y with
      | tmul a b => simp [g]
      | add y z hy hz => simp [hy, hz, TensorProduct.add_tmul]
    have hmem : Comodule.coact (R := k) (C := A) v ∈ LinearMap.eqLocus
        (TensorProduct.AlgebraTensorModule.lTensor k V f)
        (TensorProduct.AlgebraTensorModule.lTensor k V g) := by
      rw [LinearMap.mem_eqLocus, TensorProduct.AlgebraTensorModule.coe_lTensor,
        TensorProduct.AlgebraTensorModule.coe_lTensor, hf, hg]
    rw [Module.Flat.eqLocus_lTensor_eq] at hmem
    obtain ⟨y, hy⟩ := hmem
    rw [hB]
    exact ⟨y, by rw [← hy, TensorProduct.AlgebraTensorModule.coe_lTensor]⟩
  · rintro ⟨x, hx⟩
    calc
      π.lTensor V (Comodule.coact (R := k) (C := A) v) =
          (π ∘ₗ B.subtype).lTensor V x := by rw [← hx, LinearMap.lTensor_comp_apply]
      _ = (Algebra.linearMap k Q ∘ₗ Coalgebra.counit ∘ₗ B.subtype).lTensor V x := by
        rw [mkₐ_toLinearMap_comp_subtype_coinvariants]
      _ = (Algebra.linearMap k Q).lTensor V
          (Coalgebra.counit.lTensor V (B.subtype.lTensor V x)) := by
            rw [LinearMap.lTensor_comp_apply, LinearMap.lTensor_comp_apply]
      _ = (Algebra.linearMap k Q).lTensor V
          (Coalgebra.counit.lTensor V (Comodule.coact (R := k) (C := A) v)) := by rw [hx]
      _ = v ⊗ₜ[k] (1 : Q) := by rw [Comodule.lTensor_counit_coact]; simp

/-- **Invariants of a normal subgroup are stable under the ambient group.** Over a field, the
coaction maps a vector fixed by the normal closed subgroup cut out by `I` into the tensor product
of those fixed vectors with `A`. -/
theorem IsNormal.coact_mem_range_rTensor_weightSpace_one (hI : I.IsNormal) {v : V}
    (hv : v ∈ I.weightSpace V 1) :
    Comodule.coact (R := k) (C := A) v ∈
      LinearMap.range ((I.weightSpace V 1).subtype.rTensor A) := by
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  let Q := A ⧸ I.toIdeal
  let B := Subalgebra.toSubmodule I.coinvariants
  let π : A →ₗ[k] Q := (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap
  let F : V →ₗ[k] V ⊗[k] Q :=
    π.lTensor V ∘ₗ Comodule.coact (R := k) (C := A) - (TensorProduct.mk k V Q).flip 1
  have hW : I.weightSpace V 1 = LinearMap.ker F := by
    ext w
    simp [F, π, mem_weightSpace, sub_eq_zero, LinearMap.lTensor]
  obtain ⟨x, hx⟩ := mem_weightSpace_one_iff_coact_mem_range.1 hv
  -- Coinvariants of a normal Hopf ideal are left coinvariants.
  have hleft : π.rTensor A ∘ₗ Coalgebra.comul ∘ₗ B.subtype =
      TensorProduct.mk k Q A 1 ∘ₗ B.subtype := by
    ext ⟨b, hb⟩
    simpa using IsNormal.rTensor_mkₐ_comul_of_mem_coinvariants
      (H := _root_.CommHopfAlgCat.of k A) (I := I) hI ((Subalgebra.mem_toSubmodule _).1 hb)
  -- Restricting the matrix coefficients of `v` to the subgroup gives the trivial coaction.
  have hF : F.rTensor A (Comodule.coact (R := k) (C := A) v) = 0 := by
    have hsub : F.rTensor A (Comodule.coact (R := k) (C := A) v) =
        (π.lTensor V ∘ₗ Comodule.coact (R := k) (C := A)).rTensor A
            (Comodule.coact (R := k) (C := A) v) -
          ((TensorProduct.mk k V Q).flip 1).rTensor A (Comodule.coact (R := k) (C := A) v) := by
      simp only [F, LinearMap.rTensor_sub]
      -- Subtraction of linear maps evaluates pointwise by definition.
      rfl
    apply (TensorProduct.assoc k V Q A).injective
    rw [hsub, map_sub,
      assoc_rTensor_coact_eq_lTensor_one_of_mem_range B π hx hleft,
      LinearMap.assoc_flip_mk_rTensor, sub_self, map_zero]
  have hexact := LinearMap.exact_iff.mp
    (Module.Flat.rTensor_exact A (LinearMap.exact_subtype_ker_map F))
  rw [hW, ← hexact]
  exact hF

variable (V) in
/-- **The invariants of a normal closed subgroup form an ambient subrepresentation.** Over a
field, the vectors fixed by the normal closed subgroup cut out by `I` form a subcomodule. Neither
the ambient group nor the subgroup needs to be reduced or of finite type. -/
noncomputable def IsNormal.weightSpaceOneSubcomodule (hI : I.IsNormal) : Subcomodule k A V :=
  Subcomodule.ofSubmodule (I.weightSpace V 1) fun _ hv ↦
    hI.coact_mem_range_rTensor_weightSpace_one hv

/-- Normal-subgroup invariants are the weight space of the trivial character. -/
@[simp]
theorem IsNormal.weightSpaceOneSubcomodule_toSubmodule (hI : I.IsNormal) :
    (hI.weightSpaceOneSubcomodule V).toSubmodule = I.weightSpace V 1 :=
  (rfl)

/-- The weight-space and subcomodule presentations of normal-subgroup invariants are linearly
equivalent. -/
noncomputable def IsNormal.weightSpaceOneLinearEquiv (hI : I.IsNormal) :
    I.weightSpace V 1 ≃ₗ[k] hI.weightSpaceOneSubcomodule V :=
  LinearEquiv.ofEq _ _ hI.weightSpaceOneSubcomodule_toSubmodule.symm

/-- The invariant-vector equivalence preserves the underlying ambient vector. -/
@[simp]
theorem IsNormal.coe_weightSpaceOneLinearEquiv_apply (hI : I.IsNormal)
    (v : I.weightSpace V 1) :
    (hI.weightSpaceOneLinearEquiv v : V) = v := by
  rfl

/-- An ambient vector belongs to the normal-subgroup invariant representation precisely when
its coaction restricts to the trivial coaction on the subgroup. -/
@[simp]
theorem IsNormal.mem_weightSpaceOneSubcomodule (hI : I.IsNormal) {v : V} :
    v ∈ hI.weightSpaceOneSubcomodule V ↔
      TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap
          (Comodule.coact (R := k) (C := A) v) = v ⊗ₜ[k] (1 : A ⧸ I.toIdeal) := by
  rw [← Subcomodule.mem_toSubmodule, hI.weightSpaceOneSubcomodule_toSubmodule,
    mem_weightSpace, GroupLike.val_one]

/-- **The quotient group acts on the invariants of a normal subgroup.** Over a field, the coaction
on the vectors fixed by a normal closed subgroup has coefficients in the coinvariants of `I`, the
coordinate ring of the quotient group. -/
theorem IsNormal.coact_mem_range_lTensor_coinvariants (hI : I.IsNormal)
    (w : hI.weightSpaceOneSubcomodule V) :
    Comodule.coact (R := k) (C := A) w ∈ LinearMap.range
      ((Subalgebra.toSubmodule I.coinvariants).subtype.lTensor
        (hI.weightSpaceOneSubcomodule V)) := by
  let _ : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  have hrange : Comodule.coact (R := k) (C := A) (w : V) ∈
      LinearMap.range (TensorProduct.map (I.weightSpace V 1).subtype
        (Subalgebra.toSubmodule I.coinvariants).subtype) := by
    rw [Submodule.range_map_subtype_subtype]
    exact ⟨mem_weightSpace_one_iff_coact_mem_range.1 w.2,
      hI.coact_mem_range_rTensor_weightSpace_one w.2⟩
  obtain ⟨z, hz⟩ := hrange
  let W := hI.weightSpaceOneSubcomodule V
  let e := hI.weightSpaceOneLinearEquiv (V := V)
  have he : (SMulMemClass.subtype W : W →ₗ[k] V) ∘ₗ e.toLinearMap =
      (I.weightSpace V 1).subtype := by
    ext x
    exact hI.coe_weightSpaceOneLinearEquiv_apply x
  refine ⟨e.toLinearMap.rTensor _ z, ?_⟩
  apply Module.Flat.rTensor_preserves_injective_linearMap (SMulMemClass.subtype W)
    Subtype.val_injective
  rw [Subcomodule.subtype_rTensor_coact, ← hz, ← LinearMap.comp_apply (LinearMap.lTensor _ _),
    LinearMap.lTensor_comp_rTensor, ← LinearMap.comp_apply, LinearMap.rTensor_comp_map, he]

/-- Every algebra-valued subgroup point fixes the scalar extension of an invariant vector. -/
theorem IsNormal.endOfPoint_comp_mkₐ_tmul_of_mem_weightSpaceOneSubcomodule
    (hI : I.IsNormal) {B : Type*} [CommSemiring B] [Algebra k B]
    (g : A ⧸ I.toIdeal →ₐ[k] B) (b : B) {v : V}
    (hv : v ∈ hI.weightSpaceOneSubcomodule V) :
    Comodule.endOfPoint V (g.comp (Ideal.Quotient.mkₐ k I.toIdeal)) (b ⊗ₜ[k] v) =
      b ⊗ₜ[k] v := by
  have hv' : v ∈ I.weightSpace V 1 := by
    simpa only [← Subcomodule.mem_toSubmodule, hI.weightSpaceOneSubcomodule_toSubmodule] using hv
  simpa only [GroupLike.val_one, map_one, mul_one] using
    endOfPoint_comp_mkₐ_tmul_of_mem_weightSpace g b hv'

end Field

namespace IsNormal

variable {I : HopfIdeal R H}

/-- Every ambient base-valued point sends a base-point-fixed vector to another base-point-fixed
vector. -/
theorem basePointsRepresentation_mem_basePointFixedSubmodule (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {m : M} (hm : m ∈ I.basePointFixedSubmodule M) :
    Comodule.basePointsRepresentation (R := R) (H := H) M g m ∈
      I.basePointFixedSubmodule M := by
  let N := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
    (CommAlgCat.of R R)
  let _ : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R H) I hI (CommAlgCat.of R R)
  have hm' : m ∈ Representation.invariants
      ((Comodule.basePointsRepresentation (R := R) (H := H) M).comp N.subtype) := by
    simpa only [basePointFixedSubmodule_def] using hm
  have hstable := Representation.le_comap_invariants
    (Comodule.basePointsRepresentation (R := R) (H := H) M) N g hm'
  simpa only [Submodule.mem_comap, basePointFixedSubmodule_def] using hstable

variable (M) in
/-- The representation of the full group of base-valued points on the vectors fixed by the point
subgroup cut out by the normal Hopf ideal `I`. Normality makes this submodule ambient-stable. -/
noncomputable abbrev basePointFixedSubrepresentation (hI : I.IsNormal) :
    Representation R
      (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
      (I.basePointFixedSubmodule M) := by
  rw [basePointFixedSubmodule_def]
  let N := CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
    (CommAlgCat.of R R)
  let _ : N.Normal := CommHopfAlgCat.quotientPointsSubgroup_normal
    (_root_.CommHopfAlgCat.of R H) I hI (CommAlgCat.of R R)
  exact Representation.toInvariants
    (Comodule.basePointsRepresentation (R := R) (H := H) M)
    N

/-- The scalar extension of the base-point-fixed submodule is stable under every ambient point
endomorphism. -/
theorem endOfPoint_le_comap_basePointFixedSubmodule_baseChange (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.basePointFixedSubmodule M).baseChange R ≤
      ((I.basePointFixedSubmodule M).baseChange R).comap (Comodule.endOfPoint M g.ofConv) := by
  rw [Submodule.baseChange_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, TensorProduct.mk_apply]
  rw [Comodule.endOfPoint_tmul, one_smul,
    Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
  exact Submodule.subset_span
    ⟨_, basePointsRepresentation_mem_basePointFixedSubmodule hI g hm, rfl⟩

/-- Scalar-extension form of the stability of normal-subgroup fixed vectors. This is the shape
needed by geometric point-separation criteria for promoting a submodule to a subcomodule. -/
theorem endOfPoint_one_tmul_mem_basePointFixedSubmodule_baseChange (hI : I.IsNormal)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    {m : M} (hm : m ∈ I.basePointFixedSubmodule M) :
    Comodule.endOfPoint M g.ofConv (1 ⊗ₜ[R] m) ∈
      (I.basePointFixedSubmodule M).baseChange R :=
  endOfPoint_le_comap_basePointFixedSubmodule_baseChange hI g
    (Submodule.tmul_mem_baseChange_of_mem _ hm)

end IsNormal

end HopfIdeal

end

end TauCeti
