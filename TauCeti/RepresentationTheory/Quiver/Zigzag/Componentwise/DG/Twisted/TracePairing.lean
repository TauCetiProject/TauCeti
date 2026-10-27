/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Trace
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.TracePairing

/-!
# Cochain trace pairings on finite formal twisted zigzag objects

The source supertrace of actual enriched composition gives a pairing of complementary
Hom-complex terms over a commutative ring. Its coefficients are arbitrary and its definition
uses a selected presentation of the source object. A selected presentation of the target gives
a matrix formula through the generator unit pairing, with the source diagonal sign and the
actual shifted-composition sign.

Over a field, nonzero coefficients on the selected source rows give a perfect pairing of
these terms. Both objects may carry arbitrary Maurer–Cartan twists; their twisted differentials
need not vanish. The source-row condition is sufficient in every degree.

## References

* The actual formal trace and evaluation are `TauCeti.ZigzagProjectiveTwistedClosure.trace`
  and `TauCeti.ZigzagProjectiveTwistedClosure.trace_apply` in
  `TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Trace`.
* The generator input is `TauCeti.zigzagAlgebraProjectiveDGHomWeightedTracePairing` with its
  perfectness and evaluation in
  `TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.TracePairing`.
* Term finiteness is `TauCeti.ZigzagProjectiveTwistedClosure.moduleFinite_dgHom` in
  `TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Closure`.
-/

public section
noncomputable section
namespace TauCeti
namespace ZigzagProjectiveTwistedClosure
open CategoryTheory
universe u
variable (k : Type u) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra
local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "E" => zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G
local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "𝒱" => DGFullSubcategory (fun M ↦ ∃ i : V, M = D i)
local notation "𝒮" => DGShiftClosure 𝒱

/-- The source supertrace of actual complementary-degree enriched composition. -/
def tracePairing (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (p : ℤ) :
    DGHom k p X Y →ₗ[k] DGHom k (2 - p) Y X →ₗ[k] k where
  toFun f :=
    { toFun := fun g ↦ trace k G c X v hv (dgComp k f g (by omega))
      map_add' := fun g h ↦ by rw [dgComp_add, map_add]
      map_smul' := fun a g ↦ by
        simp only [dgComp_smul, map_smul, RingHom.id_apply] }
  map_add' f h := by
    ext g
    change trace k G c X v hv (dgComp k (f + h) g (by omega)) =
      trace k G c X v hv (dgComp k f g (by omega)) +
        trace k G c X v hv (dgComp k h g (by omega))
    rw [add_dgComp, map_add]
  map_smul' a f := by
    ext g
    change trace k G c X v hv (dgComp k (a • f) g (by omega)) =
      a • trace k G c X v hv (dgComp k f g (by omega))
    rw [smul_dgComp, map_smul]

/-- Evaluation of the bilinear map is the actual composite supertrace. -/
@[simp]
theorem tracePairing_apply (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (p : ℤ)
    (f : DGHom k p X Y) (g : DGHom k (2 - p) Y X) :
    tracePairing k G c X Y v hv p f g = trace k G c X v hv (dgComp k f g (by omega)) := by
  simp only [tracePairing, LinearMap.coe_mk, AddHom.coe_mk]

private theorem tracePairing_entry (c : V → k) (p : ℤ)
    (S T : 𝒮) (a b : V) (hS : S.obj.obj = D a) (hT : T.obj.obj = D b)
    (x : DGHom k p S T) (y : DGHom k (2 - p) T S) :
  let F : DGHom k p S T ≃ₗ[k] DGHom k (p + (T.shift - S.shift)) (D a) (D b) :=
    (DGShiftClosure.dgHomEquiv k S T p).trans
      (eqToIso (congrArg₂ (fun A B ↦ (dgHomComplex k A B).X (p + (T.shift - S.shift)))
        hS hT)).toLinearEquiv;
  let H : DGHom k (2 - p) T S ≃ₗ[k]
      DGHom k (2 - (p + (T.shift - S.shift))) (D b) (D a) :=
    (DGShiftClosure.dgHomEquiv k T S (2 - p)).trans
      ((eqToIso (congrArg₂
        (fun A B ↦ (dgHomComplex k A B).X ((2 - p) + (S.shift - T.shift)))
        hT hS)).toLinearEquiv.trans
          ((dgHomComplex k (D b) (D a)).XIsoOfEq (by omega)).toLinearEquiv);
    S.shift.negOnePow • (c a * zigzagAlgebraTrace k G
      (E a a 2 (castDeg k (by omega)
        ((eqToIso (congrArg₂
          (fun A B ↦ (dgHomComplex k A B).X (2 + (S.shift - S.shift)))
          hS hS)).hom.hom
            (DGShiftClosure.dgHomEquiv k S S 2 (dgComp k x y (by omega))))) : Z)) =
      (S.shift + (S.shift - T.shift) * (p + (T.shift - S.shift))).negOnePow •
        (c a * zigzagAlgebraProjectiveDGHomWeightedTracePairing k G (fun _ ↦ 1)
          a b (p + (T.shift - S.shift)) (F x) (H y)) := by
  -- Substitute the endpoint presentations before applying the shift formula.
  rcases S with ⟨⟨M, hM⟩, r⟩
  rcases T with ⟨⟨N, hN⟩, s⟩
  dsimp only at hS hT
  subst M N
  dsimp only
  simp only [eqToIso_refl, Iso.refl_hom,
    ModuleCat.hom_id, LinearMap.id_apply, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply, ← castDeg_def]
  erw [DGShiftClosure.dgHomEquiv_dgComp k x y (by omega)]
  rw [DGFullSubcategory.dgComp_eq]
  have hcoe (P : Submodule k Z) (u : ℤˣ) (z : P) :
      (↑(u • z) : Z) = u • (z : Z) :=
    map_zsmul_unit P.subtype u z
  simp only [map_zsmul_unit, hcoe, mul_smul_comm, smul_smul, ← Int.negOnePow_add]
  congr 1
  rw [zigzagAlgebraProjectiveDGHomWeightedTracePairing_apply]
  simp only [Units.val_one, one_mul,
    coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_apply]
  -- Complementary-degree casts are explicit public DG transports.
  erw [dgComp_castDeg k (q' := 2 - (p + (s - r)))
    (n := 2) (n' := 2) (by omega) rfl]
  erw [← castDeg_dgComp k (X := D a) (Y := D b)
    (p' := p + (s - r)) (n := 2 + (r - r)) (n' := 2) rfl (by omega)]
  · simp only [castDeg_self]
  · omega

private theorem tracePairing_eq_sum_comp
    (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (p : ℤ)
    (f : DGHom k p X Y) (g : DGHom k (2 - p) Y X) :
    tracePairing k G c X Y v hv p f g = ∑ i, ∑ j,
      (X.obj.X i).shift.negOnePow • (c (v i) * zigzagAlgebraTrace k G
        (E (v i) (v i) 2 (castDeg k (by omega)
          ((eqToIso (congrArg₂
            (fun A B ↦ (dgHomComplex k A B).X
              (2 + ((X.obj.X i).shift - (X.obj.X i).shift)))
            (hv i) (hv i))).hom.hom
              (DGShiftClosure.dgHomEquiv k (X.obj.X i) (X.obj.X i) 2
                (dgComp k
                  (DGAdditiveClosure.dgHomEquiv k X.obj Y.obj p
                    (DGTwistedObject.dgHomEquiv k X Y p f) i j)
                  (DGAdditiveClosure.dgHomEquiv k Y.obj X.obj (2 - p)
                    (DGTwistedObject.dgHomEquiv k Y X (2 - p) g) j i) (by omega))))) : Z)) := by
  classical
  let L (i : X.obj.ι) : DGHom k 2 (X.obj.X i) (X.obj.X i) →ₗ[k] k :=
    (X.obj.X i).shift.negOnePow •
      ((c (v i) • (zigzagAlgebraTrace k G).comp
        ((Submodule.subtype _).comp (E (v i) (v i) 2).toLinearMap)).comp
          ((castDeg k (X := D (v i)) (Y := D (v i))
            (p := 2 + ((X.obj.X i).shift - (X.obj.X i).shift)) (p' := 2) (by omega)).comp
              (((eqToIso (congrArg₂
                (fun A B ↦ (dgHomComplex k A B).X
                  (2 + ((X.obj.X i).shift - (X.obj.X i).shift)))
                (hv i) (hv i))).hom.hom).comp
                  (DGShiftClosure.dgHomEquiv k (X.obj.X i) (X.obj.X i) 2).toLinearMap)))
  have hL (i : X.obj.ι) (z : DGHom k 2 (X.obj.X i) (X.obj.X i)) :
      L i z = (X.obj.X i).shift.negOnePow • (c (v i) * zigzagAlgebraTrace k G
        (E (v i) (v i) 2 (castDeg k (by omega)
          ((eqToIso (congrArg₂
            (fun A B ↦ (dgHomComplex k A B).X
              (2 + ((X.obj.X i).shift - (X.obj.X i).shift)))
            (hv i) (hv i))).hom.hom
              (DGShiftClosure.dgHomEquiv k (X.obj.X i) (X.obj.X i) 2 z))) : Z)) := by
    simp only [L, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, smul_eq_mul]
  have htrace (z : DGHom k 2 X X) : trace k G c X v hv z = ∑ i,
      L i (DGAdditiveClosure.dgHomEquiv k X.obj X.obj 2
        (DGTwistedObject.dgHomEquiv k X X 2 z) i i) := by
    rw [trace_apply]
    simp only [hL]
  have hm (i : X.obj.ι) : DGAdditiveClosure.dgHomEquiv k X.obj X.obj 2
      (dgComp k (DGTwistedObject.dgHomEquiv k X Y p f)
        (DGTwistedObject.dgHomEquiv k Y X (2 - p) g) (by omega)) i i =
      ∑ j, dgComp k
        (DGAdditiveClosure.dgHomEquiv k X.obj Y.obj p
          (DGTwistedObject.dgHomEquiv k X Y p f) i j)
        (DGAdditiveClosure.dgHomEquiv k Y.obj X.obj (2 - p)
          (DGTwistedObject.dgHomEquiv k Y X (2 - p) g) j i) (by omega) :=
    DGAdditiveClosure.dgHomEquiv_dgComp k
      (DGTwistedObject.dgHomEquiv k X Y p f)
      (DGTwistedObject.dgHomEquiv k Y X (2 - p) g) (by omega) i i
  conv_lhs =>
    rw [tracePairing_apply k G c X Y v hv p f g, htrace,
      DGTwistedObject.dgHomEquiv_dgComp k f g (by omega)]
    simp only [hm, map_sum]
  simp only [hL]

/-- Each matrix contribution is the generator unit pairing with its actual two shift signs. -/
theorem tracePairing_eq_sum
    (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (w : Y.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (p : ℤ)
    (f : DGHom k p X Y) (g : DGHom k (2 - p) Y X) :
  let F (i : X.obj.ι) (j : Y.obj.ι) : DGHom k p (X.obj.X i) (Y.obj.X j) ≃ₗ[k] DGHom k (p + ((Y.obj.X
    j).shift - (X.obj.X i).shift)) (D (v i)) (D (w j)) :=
    (DGShiftClosure.dgHomEquiv k (X.obj.X i) (Y.obj.X j) p).trans
      (eqToIso (congrArg₂ (fun A B ↦ (dgHomComplex k A B).X (p + ((Y.obj.X j).shift - (X.obj.X
        i).shift)))
        (hv i) (hw j))).toLinearEquiv;
  let H (i : X.obj.ι) (j : Y.obj.ι) : DGHom k (2 - p) (Y.obj.X j) (X.obj.X i) ≃ₗ[k]
      DGHom k (2 - (p + ((Y.obj.X j).shift - (X.obj.X i).shift))) (D (w j)) (D (v i)) :=
    (DGShiftClosure.dgHomEquiv k (Y.obj.X j) (X.obj.X i) (2 - p)).trans
      ((eqToIso (congrArg₂
        (fun A B ↦ (dgHomComplex k A B).X ((2 - p) + ((X.obj.X i).shift - (Y.obj.X j).shift)))
        (hw j) (hv i))).toLinearEquiv.trans
          ((dgHomComplex k (D (w j)) (D (v i))).XIsoOfEq (by omega)).toLinearEquiv);
    tracePairing k G c X Y v hv p f g = ∑ i, ∑ j,
      ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
          (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
        (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing k G (fun _ ↦ 1)
          (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
          (F i j (DGAdditiveClosure.dgHomEquiv k X.obj Y.obj p
            (DGTwistedObject.dgHomEquiv k X Y p f) i j))
          (H i j (DGAdditiveClosure.dgHomEquiv k Y.obj X.obj (2 - p)
            (DGTwistedObject.dgHomEquiv k Y X (2 - p) g) j i))) := by
  classical
  rw [tracePairing_eq_sum_comp k G c X Y v hv p f g]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact tracePairing_entry k G c p (X.obj.X i) (Y.obj.X j) (v i) (w j) (hv i) (hw j)
    (DGAdditiveClosure.dgHomEquiv k X.obj Y.obj p
      (DGTwistedObject.dgHomEquiv k X Y p f) i j)
    (DGAdditiveClosure.dgHomEquiv k Y.obj X.obj (2 - p)
      (DGTwistedObject.dgHomEquiv k Y X (2 - p) g) j i)

section Field
/-- Opposite-entry tests separate the first actual Hom term. -/
private theorem tracePairing_injective (K : Type u) [Field K] (G : SimpleGraph V)
    (c : V → K) (X Y : ZigzagProjectiveTwistedClosure K G)
    (v : X.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = zigzagAlgebraProjectiveDGRightModule K G (v i))
    (hc : ∀ i, c (v i) ≠ 0) (p : ℤ) :
    Function.Injective (tracePairing K G c X Y v hv p) := by
  classical
  choose w hw using fun j : Y.obj.ι ↦ (Y.obj.X j).obj.property
  let F (i : X.obj.ι) (j : Y.obj.ι) : DGHom K p (X.obj.X i) (Y.obj.X j) ≃ₗ[K] DGHom K (p + ((Y.obj.X
    j).shift - (X.obj.X i).shift)) (zigzagAlgebraProjectiveDGRightModule K G (v i))
    (zigzagAlgebraProjectiveDGRightModule K G (w j)) :=
    (DGShiftClosure.dgHomEquiv K (X.obj.X i) (Y.obj.X j) p).trans
      (eqToIso (congrArg₂ (fun A B ↦ (dgHomComplex K A B).X (p + ((Y.obj.X j).shift - (X.obj.X
        i).shift)))
        (hv i) (hw j))).toLinearEquiv
  let H (i : X.obj.ι) (j : Y.obj.ι) : DGHom K (2 - p) (Y.obj.X j) (X.obj.X i) ≃ₗ[K]
      DGHom K (2 - (p + ((Y.obj.X j).shift - (X.obj.X i).shift)))
        (zigzagAlgebraProjectiveDGRightModule K G (w j)) (zigzagAlgebraProjectiveDGRightModule K G
        (v i)) :=
    (DGShiftClosure.dgHomEquiv K (Y.obj.X j) (X.obj.X i) (2 - p)).trans
      ((eqToIso (congrArg₂
        (fun A B ↦ (dgHomComplex K A B).X ((2 - p) + ((X.obj.X i).shift - (Y.obj.X j).shift)))
        (hw j) (hv i))).toLinearEquiv.trans
          ((dgHomComplex K (zigzagAlgebraProjectiveDGRightModule K G (w j))
            (zigzagAlgebraProjectiveDGRightModule K G (v i))).XIsoOfEq (by omega)).toLinearEquiv)
  let A := (DGTwistedObject.dgHomEquiv K X Y p).trans
    (DGAdditiveClosure.dgHomEquiv K X.obj Y.obj p)
  let B := (DGTwistedObject.dgHomEquiv K Y X (2 - p)).trans
    (DGAdditiveClosure.dgHomEquiv K Y.obj X.obj (2 - p))
  have heval (f : DGHom K p X Y) (g : DGHom K (2 - p) Y X) :
      tracePairing K G c X Y v hv p f g = ∑ i, ∑ j,
        ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
          (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            (F i j (A f i j)) (H i j (B g j i))) :=
    tracePairing_eq_sum K G c X Y v w hv hw p f g
  intro f₁ f₂ h
  apply A.injective
  funext i j
  apply (F i j).injective
  apply (LinearMap.IsPerfPair.bijective_left
    (zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
      (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift)))).injective
  apply LinearMap.ext
  intro b
  let t : DGHom K (2 - p) Y X := B.symm (Pi.single j (Pi.single i ((H i j).symm b)))
  have ht := LinearMap.congr_fun h t
  change tracePairing K G c X Y v hv p f₁ t =
    tracePairing K G c X Y v hv p f₂ t at ht
  have hsame : B t j i = (H i j).symm b := by simp [t]
  have hrow (j' : Y.obj.ι) (hj : j' ≠ j) (i' : X.obj.ι) : B t j' i' = 0 := by
    simp [t, Pi.single_eq_of_ne hj]
  have hcol (i' : X.obj.ι) (hi : i' ≠ i) : B t j i' = 0 := by
    simp [t, Pi.single_eq_of_ne hi]
  have htest (f : DGHom K p X Y) : tracePairing K G c X Y v hv p f t =
      ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
        (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            (F i j (A f i j)) b) := by
    rw [heval]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp only [hsame, LinearEquiv.apply_symm_apply]
      · intro j' _ hj
        simp [hrow j' hj]
      · simp
    · intro i' _ hi
      apply Finset.sum_eq_zero
      intro j' _
      by_cases hj : j' = j
      · subst j'
        simp [hcol i' hi]
      · simp [hrow j' hj]
    · simp
  have hisolate :
      ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
        (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            (F i j (A f₁ i j)) b) =
      ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
        (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            (F i j (A f₂ i j)) b) := by
    simpa only [htest] using ht
  apply mul_left_cancel₀ (hc i)
  have hu := congrArg (fun z : K ↦
    (((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
      (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow)⁻¹ • z) hisolate
  simpa only [inv_smul_smul, LinearMap.flip_apply] using hu

private theorem tracePairing_flip_injective (K : Type u) [Field K] (G : SimpleGraph V)
    (c : V → K) (X Y : ZigzagProjectiveTwistedClosure K G)
    (v : X.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = zigzagAlgebraProjectiveDGRightModule K G (v i))
    (hc : ∀ i, c (v i) ≠ 0) (p : ℤ) :
    Function.Injective (tracePairing K G c X Y v hv p).flip := by
  classical
  choose w hw using fun j : Y.obj.ι ↦ (Y.obj.X j).obj.property
  let F (i : X.obj.ι) (j : Y.obj.ι) : DGHom K p (X.obj.X i) (Y.obj.X j) ≃ₗ[K] DGHom K (p + ((Y.obj.X
    j).shift - (X.obj.X i).shift)) (zigzagAlgebraProjectiveDGRightModule K G (v i))
    (zigzagAlgebraProjectiveDGRightModule K G (w j)) :=
    (DGShiftClosure.dgHomEquiv K (X.obj.X i) (Y.obj.X j) p).trans
      (eqToIso (congrArg₂ (fun A B ↦ (dgHomComplex K A B).X (p + ((Y.obj.X j).shift - (X.obj.X
        i).shift)))
        (hv i) (hw j))).toLinearEquiv
  let H (i : X.obj.ι) (j : Y.obj.ι) : DGHom K (2 - p) (Y.obj.X j) (X.obj.X i) ≃ₗ[K]
      DGHom K (2 - (p + ((Y.obj.X j).shift - (X.obj.X i).shift)))
        (zigzagAlgebraProjectiveDGRightModule K G (w j)) (zigzagAlgebraProjectiveDGRightModule K G
        (v i)) :=
    (DGShiftClosure.dgHomEquiv K (Y.obj.X j) (X.obj.X i) (2 - p)).trans
      ((eqToIso (congrArg₂
        (fun A B ↦ (dgHomComplex K A B).X ((2 - p) + ((X.obj.X i).shift - (Y.obj.X j).shift)))
        (hw j) (hv i))).toLinearEquiv.trans
          ((dgHomComplex K (zigzagAlgebraProjectiveDGRightModule K G (w j))
            (zigzagAlgebraProjectiveDGRightModule K G (v i))).XIsoOfEq (by omega)).toLinearEquiv)
  let A := (DGTwistedObject.dgHomEquiv K X Y p).trans
    (DGAdditiveClosure.dgHomEquiv K X.obj Y.obj p)
  let B := (DGTwistedObject.dgHomEquiv K Y X (2 - p)).trans
    (DGAdditiveClosure.dgHomEquiv K Y.obj X.obj (2 - p))
  have heval (f : DGHom K p X Y) (g : DGHom K (2 - p) Y X) :
      tracePairing K G c X Y v hv p f g = ∑ i, ∑ j,
        ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
          (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            (F i j (A f i j)) (H i j (B g j i))) :=
    tracePairing_eq_sum K G c X Y v w hv hw p f g
  intro g₁ g₂ h
  apply B.injective
  funext j i
  apply (H i j).injective
  apply (LinearMap.IsPerfPair.bijective_right
    (zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
      (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift)))).injective
  apply LinearMap.ext
  intro a
  let t : DGHom K p X Y := A.symm (Pi.single i (Pi.single j ((F i j).symm a)))
  have ht := LinearMap.congr_fun h t
  simp only [LinearMap.flip_apply] at ht
  change tracePairing K G c X Y v hv p t g₁ =
    tracePairing K G c X Y v hv p t g₂ at ht
  have hsame : A t i j = (F i j).symm a := by simp [t]
  have hrow (i' : X.obj.ι) (hi : i' ≠ i) (j' : Y.obj.ι) : A t i' j' = 0 := by
    simp [t, Pi.single_eq_of_ne hi]
  have hcol (j' : Y.obj.ι) (hj : j' ≠ j) : A t i j' = 0 := by
    simp [t, Pi.single_eq_of_ne hj]
  have htest (g : DGHom K (2 - p) Y X) : tracePairing K G c X Y v hv p t g =
      ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
        (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            a (H i j (B g j i))) := by
    rw [heval]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp only [hsame, LinearEquiv.apply_symm_apply]
      · intro j' _ hj
        simp [hcol j' hj]
      · simp
    · intro i' _ hi
      apply Finset.sum_eq_zero
      intro j' _
      simp [hrow i' hi]
    · simp
  have hisolate :
      ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
        (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            a (H i j (B g₁ j i))) =
      ((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
        (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
          (c (v i) * zigzagAlgebraProjectiveDGHomWeightedTracePairing K G (fun _ ↦ 1)
            (v i) (w j) (p + ((Y.obj.X j).shift - (X.obj.X i).shift))
            a (H i j (B g₂ j i))) := by
    simpa only [htest] using ht
  apply mul_left_cancel₀ (hc i)
  have hu := congrArg (fun z : K ↦
    (((X.obj.X i).shift + ((X.obj.X i).shift - (Y.obj.X j).shift) *
      (p + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow)⁻¹ • z) hisolate
  simpa only [inv_smul_smul, LinearMap.flip_apply] using hu

/-- Nonzero selected source coefficients give a perfect pairing of every actual Hom term. -/
theorem tracePairing_isPerfPair (K : Type u) [Field K] (G : SimpleGraph V)
    (c : V → K) (X Y : ZigzagProjectiveTwistedClosure K G)
    (v : X.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = zigzagAlgebraProjectiveDGRightModule K G (v i))
    (hc : ∀ i, c (v i) ≠ 0) (p : ℤ) :
    (tracePairing K G c X Y v hv p).IsPerfPair := by
  exact LinearMap.IsPerfPair.of_injective
    (tracePairing_injective K G c X Y v hv hc p)
    (tracePairing_flip_injective K G c X Y v hv hc p)

end Field
end ZigzagProjectiveTwistedClosure
end TauCeti
