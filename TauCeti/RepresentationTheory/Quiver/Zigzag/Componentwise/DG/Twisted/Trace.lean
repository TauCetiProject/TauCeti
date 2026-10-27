/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Closure
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.WeightedTrace

/-!
# Supertraces on the formal twisted closure of zigzag projectives

The diagonal trace on a summand shifted by an integer r is multiplied by r.negOnePow.
Together with opposite vertex weights on selected edges this makes degree-one matrix
composition anticyclic, hence kills the commutator differential of an arbitrary MC twist.
The descended functional uses the existing canonical cohomology maps.

The corner calculation reuses `TauCeti.zigzagAlgebraTrace_weighted_mul_flip` from
`TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.WeightedTrace`.
The diagonal weighting transports this graded cyclicity to homogeneous DG cochains and
MC matrix traces using `DGShiftClosure.dgHomEquiv_dgComp` and the differential formula in
`TauCeti.CategoryTheory.DG.ShiftClosure.Basic`.

This construction concerns the existing formal closure. It supplies neither perfectness nor
the naturality or triangulated realization required for an all-object Serre identification.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.ZigzagProjectiveTwistedClosure

universe u

variable (k : Type u) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "E" => zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G
local notation "𝒱" => DGFullSubcategory (fun M ↦ ∃ i : V, M = D i)
local notation "𝒮" => DGShiftClosure 𝒱

private def homCongr {M M' N N' : DGRightModuleCat.{u, u, u}
      (IsDGAlgebra.gradedOpposite (G := zigzagAlgebraInternalGrading k G)
        (isDGAlgebra_zero (zigzagAlgebraInternalGrading k G).piece))}
    (hM : M = M') (hN : N = N') (n : ℤ) :
    DGHom k n M N ≃ₗ[k] DGHom k n M' N' :=
  (eqToIso (congrArg₂ (fun A B ↦ (dgHomComplex k A B).X n) hM hN)).toLinearEquiv

private theorem homCongr_comp {M M' N N' P P' : DGRightModuleCat.{u, u, u}
      (IsDGAlgebra.gradedOpposite (G := zigzagAlgebraInternalGrading k G)
        (isDGAlgebra_zero (zigzagAlgebraInternalGrading k G).piece))}
    (hM : M = M') (hN : N = N') (hP : P = P') {p q n : ℤ}
    (f : DGHom k p M N) (g : DGHom k q N P) (h : p + q = n) :
    homCongr k G hM hP n (dgComp k f g h) =
      dgComp k (homCongr k G hM hN p f) (homCongr k G hN hP q g) h := by
  subst M' N' P'
  rfl

private def entryHomEquiv (X Y : 𝒮) (i j : V)
    (hX : X.obj.obj = D i) (hY : Y.obj.obj = D j) (n : ℤ) :
    DGHom k n X Y ≃ₗ[k] DGHom k (n + (Y.shift - X.shift)) (D i) (D j) :=
  (DGShiftClosure.dgHomEquiv k X Y n).trans
    (homCongr k G hX hY (n + (Y.shift - X.shift)))

private def diagonalHomEquiv (X : 𝒮) (i : V) (hX : X.obj.obj = D i) :
    DGHom k 2 X X ≃ₗ[k] DGHom k 2 (D i) (D i) :=
  (entryHomEquiv k G X X i i hX hX 2).trans
    ((dgHomComplex k (D i) (D i)).XIsoOfEq (by omega)).toLinearEquiv

private theorem shiftComp_one_one (r s : ℤ) :
    ((r - s) * (1 + (s - r))).negOnePow = 1 := by
  rw [show (r - s) * (1 + (s - r)) =
    -((s - r) + (s - r) * (s - r)) by ring]
  rw [Int.negOnePow_neg, Int.negOnePow_add, Int.negOnePow_mul_self,
    Int.units_mul_self]

private theorem supertraceSign (r s : ℤ) :
    r.negOnePow * ((1 + (s - r)) * (2 - (1 + (s - r)))).negOnePow =
      -s.negOnePow := by
  rw [show (1 + (s - r)) * (2 - (1 + (s - r))) =
    2 * (1 + (s - r)) - (1 + (s - r)) * (1 + (s - r)) by ring]
  rw [Int.negOnePow_sub, Int.negOnePow_two_mul, Int.negOnePow_mul_self, one_mul,
    ← Int.negOnePow_add, show r + (1 + (s - r)) = s + 1 by ring,
    Int.negOnePow_succ]

private theorem diagonalHomEquiv_comp_one_one (X Y : 𝒮) (i j : V)
    (hX : X.obj.obj = D i) (hY : Y.obj.obj = D j)
    (f : DGHom k 1 X Y) (g : DGHom k 1 Y X) :
    diagonalHomEquiv k G X i hX (dgComp k f g rfl) =
      dgComp k (entryHomEquiv k G X Y i j hX hY 1 f)
        (entryHomEquiv k G Y X j i hY hX 1 g) (by omega) := by
  simp only [diagonalHomEquiv, entryHomEquiv, LinearEquiv.trans_apply,
    Iso.toLinearEquiv_apply, ← castDeg_def, DGShiftClosure.dgHomEquiv_dgComp,
    DGFullSubcategory.dgComp_eq,
    shiftComp_one_one, one_smul]
  rw [homCongr_comp k G hX hY hX]
  simpa only [entryHomEquiv, LinearEquiv.trans_apply, castDeg_self] using
    (castDeg_dgComp k (p' := 1 + (Y.shift - X.shift))
      (n := 2 + (X.shift - X.shift)) (n' := 2) rfl (by omega)
      (entryHomEquiv k G X Y i j hX hY 1 f)
      (entryHomEquiv k G Y X j i hY hX 1 g) (by omega)).symm

private def vertexTrace (a : k) (i : V) : DGHom k 2 (D i) (D i) →ₗ[k] k :=
  a • (zigzagAlgebraTrace k G).comp ((Submodule.subtype _).comp (E i i 2).toLinearMap)

private theorem vertexTrace_apply (a : k) (i : V) (f : DGHom k 2 (D i) (D i)) :
    vertexTrace k G a i f = a * zigzagAlgebraTrace k G (E i i 2 f : Z) := by
  simp [vertexTrace]

private theorem vertexTrace_comp (c : V → k) (i j : V)
    (hc : G.Adj i j → c j = -c i) (d : ℤ)
    (f : DGHom k d (D i) (D j)) (g : DGHom k (2 - d) (D j) (D i)) :
    vertexTrace k G (c i) i (dgComp k f g (by omega)) =
      (d * (2 - d)).negOnePow • vertexTrace k G (c j) j (dgComp k g f (by omega)) := by
  rw [vertexTrace_apply, vertexTrace_apply,
    coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_comp,
    coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_comp]
  exact zigzagAlgebraTrace_weighted_mul_flip k G c i j hc d (E i j d f) (E j i (2 - d) g)

private def shiftedVertexTrace (a : k) (X : 𝒮) (i : V) (hX : X.obj.obj = D i) :
    DGHom k 2 X X →ₗ[k] k :=
  X.shift.negOnePow • (vertexTrace k G a i).comp (diagonalHomEquiv k G X i hX).toLinearMap

private theorem shiftedVertexTrace_comp_one_one (c : V → k) (X Y : 𝒮) (i j : V)
    (hX : X.obj.obj = D i) (hY : Y.obj.obj = D j)
    (hc : G.Adj i j → c j = -c i) (f : DGHom k 1 X Y) (g : DGHom k 1 Y X) :
    shiftedVertexTrace k G (c i) X i hX (dgComp k f g rfl) =
      -shiftedVertexTrace k G (c j) Y j hY (dgComp k g f rfl) := by
  let F := entryHomEquiv k G X Y i j hX hY 1 f
  let H := entryHomEquiv k G Y X j i hY hX 1 g
  have hcyc := vertexTrace_comp k G c i j hc (1 + (Y.shift - X.shift))
    F (castDeg k (by omega) H)
  have hfg : dgComp k (n := 2) F
      (castDeg k (p' := 2 - (1 + (Y.shift - X.shift))) (by omega) H) (by omega) =
      dgComp k (n := 2) F H (by omega) := by
    simpa only [castDeg_self] using
      (dgComp_castDeg k (q' := 2 - (1 + (Y.shift - X.shift)))
        (n := 2) (n' := 2) (by omega) rfl F H (by omega))
  have hgf : dgComp k (n := 2)
      (castDeg k (p' := 2 - (1 + (Y.shift - X.shift))) (by omega) H) F (by omega) =
      dgComp k (n := 2) H F (by omega) := by
    simpa only [castDeg_self] using
      (castDeg_dgComp k (p' := 2 - (1 + (Y.shift - X.shift)))
        (n := 2) (n' := 2) (by omega) rfl H F (by omega))
  rw [hfg, hgf] at hcyc
  dsimp only [F, H] at hcyc
  simp only [shiftedVertexTrace, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [diagonalHomEquiv_comp_one_one k G X Y i j hX hY f g,
    diagonalHomEquiv_comp_one_one k G Y X j i hY hX g f,
    hcyc, smul_smul, supertraceSign]
  simp only [Units.neg_smul]

private def matrixTrace (c : V → k) (M : DGAdditiveClosure 𝒮)
    (v : M.ι → V) (hv : ∀ i, (M.X i).obj.obj = D (v i)) : DGHom k 2 M M →ₗ[k] k where
  toFun f := ∑ i, shiftedVertexTrace k G (c (v i)) (M.X i) (v i) (hv i)
    (DGAdditiveClosure.dgHomEquiv k M M 2 f i i)
  map_add' f g := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a f := by simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

private theorem matrixTrace_comp_one_one (c : V → k) (M N : DGAdditiveClosure 𝒮)
    (v : M.ι → V) (w : N.ι → V)
    (hv : ∀ i, (M.X i).obj.obj = D (v i)) (hw : ∀ j, (N.X j).obj.obj = D (w j))
    (hc : ∀ i j, G.Adj (v i) (w j) → c (w j) = -c (v i))
    (f : DGHom k 1 M N) (g : DGHom k 1 N M) :
    matrixTrace k G c M v hv (dgComp k f g rfl) =
      -matrixTrace k G c N w hw (dgComp k g f rfl) := by
  classical
  unfold matrixTrace
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [DGAdditiveClosure.dgHomEquiv_dgComp, map_sum]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact shiftedVertexTrace_comp_one_one k G c _ _ _ _ (hv i) (hw j) (hc i j) _ _

private theorem shifted_dgDifferential_eq_zero (X Y : 𝒮) (i j : V)
    (hX : X.obj.obj = D i) (hY : Y.obj.obj = D j) (n : ℤ) (f : DGHom k n X Y) :
    dgDifferential k n f = 0 := by
  apply (DGShiftClosure.dgHomEquiv k X Y (n + 1)).injective
  rw [DGShiftClosure.dgHomEquiv_dgDifferential, map_zero]
  rw [show n + 1 + (Y.shift - X.shift) = (n + (Y.shift - X.shift)) + 1 by omega]
  have hd := DGRightModuleCat.dgDifferential_eq_zero _ _
    (by rw [hX]) (by rw [hY]) (n + (Y.shift - X.shift))
    (DGShiftClosure.dgHomEquiv k X Y n f)
  simpa only [dgDifferential, DGFullSubcategory.dgHomComplex_eq, smul_zero] using
    congrArg (fun z ↦ (Y.shift - X.shift).negOnePow • z) hd

private theorem matrix_dgDifferential_eq_zero (M : DGAdditiveClosure 𝒮)
    (v : M.ι → V) (hv : ∀ i, (M.X i).obj.obj = D (v i))
    (n : ℤ) (f : DGHom k n M M) : dgDifferential k n f = 0 := by
  apply DGAdditiveClosure.dgHom_ext k
  intro i j
  rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, map_zero, Pi.zero_apply, Pi.zero_apply]
  exact shifted_dgDifferential_eq_zero k G _ _ _ _ (hv i) (hv j) n _

/-- The degree-two supertrace on an actual finite formal twisted vertex object. -/
def trace (c : V → k) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) :
    DGHom k 2 X X →ₗ[k] k :=
  (matrixTrace k G c X.obj v hv).comp (DGTwistedObject.dgHomEquiv k X X 2).toLinearMap

/-- Each diagonal corner contributes its vertex coefficient times its formal-shift sign. -/
theorem trace_apply (c : V → k) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (f : DGHom k 2 X X) :
    trace k G c X v hv f = ∑ i, (X.obj.X i).shift.negOnePow •
      (c (v i) * zigzagAlgebraTrace k G
        (E (v i) (v i) 2
          (castDeg k (by omega)
            ((eqToIso (congrArg₂
              (fun A B ↦ (dgHomComplex k A B).X
                (2 + ((X.obj.X i).shift - (X.obj.X i).shift)))
              (hv i) (hv i))).hom.hom
              (DGShiftClosure.dgHomEquiv k (X.obj.X i) (X.obj.X i) 2
                (DGAdditiveClosure.dgHomEquiv k X.obj X.obj 2
                  (DGTwistedObject.dgHomEquiv k X X 2 f) i i)))) : Z)) := by
  simp only [trace, LinearMap.comp_apply, matrixTrace, LinearMap.coe_mk, AddHom.coe_mk,
    shiftedVertexTrace, LinearMap.smul_apply, diagonalHomEquiv, entryHomEquiv,
    LinearEquiv.trans_apply, Iso.toLinearEquiv_apply, LinearEquiv.coe_coe,
    ← castDeg_def, vertexTrace_apply, homCongr]

/-- Degree-one compositions between actual formal twisted objects have opposite supertraces. -/
theorem trace_comp_one_one (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (w : Y.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j))
    (hc : ∀ i j, G.Adj (v i) (w j) → c (w j) = -c (v i))
    (f : DGHom k 1 X Y) (g : DGHom k 1 Y X) :
    trace k G c X v hv (dgComp k f g rfl) =
      -trace k G c Y w hw (dgComp k g f rfl) := by
  simp only [trace, LinearMap.comp_apply, LinearEquiv.coe_coe,
    DGTwistedObject.dgHomEquiv_dgComp]
  exact matrixTrace_comp_one_one k G c X.obj Y.obj v w hv hw hc _ _

/-- Opposite weights at selected adjacent vertices make the supertrace kill MC boundaries. -/
theorem trace_dgDifferential (c : V → k) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i)) (f : DGHom k 1 X X) :
    trace k G c X v hv (dgDifferential k 1 f) = 0 := by
  simp only [trace, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [DGTwistedObject.dgHomEquiv_dgDifferential k 1 f]
  rw [matrix_dgDifferential_eq_zero k G X.obj v hv]
  simp only [zero_add, Int.negOnePow_one, Units.neg_smul, one_smul, map_sub, map_neg]
  rw [matrixTrace_comp_one_one k G c X.obj X.obj v v hv hv hc]
  abel

/-- The supertrace induces a functional on the existing canonical degree-two cohomology. -/
def homologyTrace (c : V → k) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i)) :
    (dgHomComplex k X X).homology 2 →ₗ[k] k := by
  let K := dgHomComplex k X X
  let tr : K.X 2 ⟶ ModuleCat.of k k := ModuleCat.ofHom (trace k G c X v hv)
  have ht : K.d 1 2 ≫ tr = 0 := by
    ext f
    exact trace_dgDifferential k G c X v hv hc f
  exact (K.homologyι 2 ≫ K.descOpcycles tr 1 (by simp) ht).hom

/-- The descended supertrace evaluates a canonical class on its representing cocycle. -/
@[simp]
theorem homologyTrace_homologyπ (c : V → k) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i))
    (z : (dgHomComplex k X X).cycles 2) :
    homologyTrace k G c X v hv hc (((dgHomComplex k X X).homologyπ 2).hom z) =
      trace k G c X v hv (((dgHomComplex k X X).iCycles 2).hom z) := by
  let K := dgHomComplex k X X
  let tr : K.X 2 ⟶ ModuleCat.of k k := ModuleCat.ofHom (trace k G c X v hv)
  have ht : K.d 1 2 ≫ tr = 0 := by
    ext f
    exact trace_dgDifferential k G c X v hv hc f
  have h : K.homologyπ 2 ≫ K.homologyι 2 ≫ K.descOpcycles tr 1 (by simp) ht =
      K.iCycles 2 ≫ tr := by
    rw [HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles]
  simpa only [K, tr, homologyTrace, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z

end TauCeti.ZigzagProjectiveTwistedClosure
