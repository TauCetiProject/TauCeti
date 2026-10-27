/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.NormNum
public import TauCeti.CategoryTheory.DG.AdditiveClosure.Basic
public import TauCeti.CategoryTheory.DG.Twisted.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.Corner.Trace
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Projective

/-!
# Closed traces on finite twisted sums of unshifted zigzag projectives

A presentation of the summands by actual vertex projectives gives a degree-two matrix trace.
The vertex coefficients may be arbitrary elements of the coefficient ring. Opposite weights
at adjacent vertices appearing in the presentation make this trace kill boundaries for every
Maurer–Cartan twist. It therefore induces a functional on canonical degree-two cohomology.

The underlying matrix differential vanishes, but the twisted differential generally does not.
Boundary vanishing follows from cancellation of its two commutator terms. Formal shifts require
an additional supertrace sign and are not part of this unshifted construction. No perfectness,
Serre functor, triangulated realization or spherical-object assertion is made here.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti

universe u

variable (k : Type u) [CommRing k] {V : Type u} [Finite V] (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "Γ" => zigzagAlgebraInternalGrading k G
private abbrev ambientDGModuleCat := DGRightModuleCat.{u, u, u}
  (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece))

local notation "𝒟" => ambientDGModuleCat k G
local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "L" => zigzagAlgebraProjectiveDGHomEquivCorner k G

private def homCongr {M M' N N' : 𝒟} (hM : M = M') (hN : N = N') (n : ℤ) :
    DGHom k n M N ≃ₗ[k] DGHom k n M' N' :=
  (eqToIso (congrArg₂ (fun A B : 𝒟 ↦ (dgHomComplex k A B).X n) hM hN)).toLinearEquiv

private theorem homCongr_comp {M M' N N' P P' : 𝒟}
    (hM : M = M') (hN : N = N') (hP : P = P')
    (f : DGHom k 1 M N) (g : DGHom k 1 N P) :
    homCongr k G hM hP 2 (dgComp k f g rfl) =
      dgComp k (homCongr k G hM hN 1 f) (homCongr k G hN hP 1 g) rfl := by
  subst M' N' P'
  rfl

private def vertexTrace (a : k) (i : V) : DGHom k 2 (D i) (D i) →ₗ[k] k :=
  a • (zigzagAlgebraTrace k G).comp
    ((Submodule.subtype _).comp (L i i (-2)).toLinearMap)

private theorem vertexTrace_apply (a : k) (i : V) (f : DGHom k 2 (D i) (D i)) :
    vertexTrace k G a i f = a * zigzagAlgebraTrace k G (L i i (-2) f : Z) := by
  simp [vertexTrace]

private theorem vertexTrace_comp_one_one (a b : k) (i j : V)
    (hc : G.Adj i j → b = -a) (f : DGHom k 1 (D i) (D j))
    (g : DGHom k 1 (D j) (D i)) :
    vertexTrace k G a i (dgComp k f g rfl) =
      -vertexTrace k G b j (dgComp k g f rfl) := by
  rw [vertexTrace_apply, vertexTrace_apply]
  have hfg := coe_zigzagAlgebraProjectiveDGHomEquivCorner_comp k G i j i (-1) (-1)
    (castDeg k (by omega) f) (castDeg k (by omega) g)
  have hgf := coe_zigzagAlgebraProjectiveDGHomEquivCorner_comp k G j i j (-1) (-1)
    (castDeg k (by omega) g) (castDeg k (by omega) f)
  norm_num only [castDeg_self] at hfg hgf
  -- The public dictionary retains the closed sum of the two internal target shifts.
  erw [hfg, hgf]
  by_cases hij : i = j
  · subst j
    have hf : (L i i (-1) f : Z) = 0 := by
      simpa using (L i i (-1) f).property
    simp [hf]
  · by_cases hadj : G.Adj i j
    · rw [hc hadj, neg_mul]
      simpa only [neg_neg] using congrArg (fun x : k ↦ a * x)
        (zigzagAlgebraTrace_mul_comm k G (L i j (-1) f : Z) (L j i (-1) g : Z))
    · have hf : (L i j (-1) f : Z) = 0 := by
        have hf := (L i j (-1) f).property.1
        rw [cornerSubmodule_zigzagAlgebra_eq_bot_of_ne_of_not_adj k G hij hadj] at hf
        exact (Submodule.mem_bot k).mp hf
      simp [hf]

private def matrixTrace (c : V → k) (M : DGAdditiveClosure 𝒟)
    (v : M.ι → V) (hv : ∀ i, M.X i = D (v i)) : DGHom k 2 M M →ₗ[k] k where
  toFun f := ∑ i, vertexTrace k G (c (v i)) (v i)
    (homCongr k G (hv i) (hv i) 2 (DGAdditiveClosure.dgHomEquiv k M M 2 f i i))
  map_add' f g := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a f := by simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

private theorem matrixTrace_comp_one_one (c : V → k) (M N : DGAdditiveClosure 𝒟)
    (v : M.ι → V) (w : N.ι → V) (hv : ∀ i, M.X i = D (v i))
    (hw : ∀ j, N.X j = D (w j))
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
  rw [homCongr_comp, homCongr_comp]
  exact vertexTrace_comp_one_one k G _ _ _ _ (hc i j) _ _

private theorem matrix_dgDifferential_eq_zero (M : DGAdditiveClosure 𝒟)
    (v : M.ι → V) (hv : ∀ i, M.X i = D (v i)) (n : ℤ) (f : DGHom k n M M) :
    dgDifferential k n f = 0 := by
  apply DGAdditiveClosure.dgHom_ext k
  intro i j
  rw [DGAdditiveClosure.dgHomEquiv_dgDifferential, map_zero, Pi.zero_apply, Pi.zero_apply]
  exact DGRightModuleCat.dgDifferential_eq_zero _ _
    (by rw [hv i]) (by rw [hv j]) n _

/-- The degree-two matrix trace of an arbitrary twist of a finite unshifted vertex sum. -/
def zigzagAlgebraFiniteTwistedTrace (c : V → k) (X : DGTwistedObject k (DGAdditiveClosure
      (DGRightModuleCat.{u, u, u}
        (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece)))))
    (v : X.obj.ι → V) (hv : ∀ i, X.obj.X i = D (v i)) : DGHom k 2 X X →ₗ[k] k :=
  (matrixTrace k G c X.obj v hv).comp (DGTwistedObject.dgHomEquiv k X X 2).toLinearMap

/-- The trace is the weighted sum of the actual diagonal degree-two corner vectors. -/
theorem zigzagAlgebraFiniteTwistedTrace_apply (c : V → k)
    (X : DGTwistedObject k (DGAdditiveClosure
      (DGRightModuleCat.{u, u, u}
        (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece)))))
    (v : X.obj.ι → V) (hv : ∀ i, X.obj.X i = D (v i)) (f : DGHom k 2 X X) :
    zigzagAlgebraFiniteTwistedTrace k G c X v hv f =
      ∑ i, c (v i) * zigzagAlgebraTrace k G
        (L (v i) (v i) (-2)
          ((eqToIso (congrArg₂ (fun A B : DGRightModuleCat.{u, u, u}
              (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece)) ↦
                (dgHomComplex k A B).X 2)
            (hv i) (hv i))).hom.hom
              (DGAdditiveClosure.dgHomEquiv k X.obj X.obj 2
                (DGTwistedObject.dgHomEquiv k X X 2 f) i i)) : Z) := by
  simp only [zigzagAlgebraFiniteTwistedTrace, LinearMap.comp_apply, matrixTrace,
    LinearMap.coe_mk, AddHom.coe_mk, vertexTrace_apply, homCongr,
    Iso.toLinearEquiv_apply, LinearEquiv.coe_coe]

/-- Opposite weights along the presentation's edges make the trace kill twisted boundaries. -/
theorem zigzagAlgebraFiniteTwistedTrace_dgDifferential (c : V → k)
    (X : DGTwistedObject k (DGAdditiveClosure
      (DGRightModuleCat.{u, u, u}
        (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece)))))
    (v : X.obj.ι → V) (hv : ∀ i, X.obj.X i = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i)) (f : DGHom k 1 X X) :
    zigzagAlgebraFiniteTwistedTrace k G c X v hv (dgDifferential k 1 f) = 0 := by
  simp only [zigzagAlgebraFiniteTwistedTrace, LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [DGTwistedObject.dgHomEquiv_dgDifferential k 1 f]
  rw [matrix_dgDifferential_eq_zero k G X.obj v hv]
  simp only [zero_add, Int.negOnePow_one, Units.neg_smul, one_smul, map_sub, map_neg]
  rw [matrixTrace_comp_one_one k G c X.obj X.obj v v hv hv hc]
  abel

/-- The closed twisted trace descends to the actual canonical degree-two cohomology module. -/
def zigzagAlgebraFiniteTwistedHomologyTrace (c : V → k)
    (X : DGTwistedObject k (DGAdditiveClosure
      (DGRightModuleCat.{u, u, u}
        (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece)))))
    (v : X.obj.ι → V) (hv : ∀ i, X.obj.X i = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i)) :
    (dgHomComplex k X X).homology 2 →ₗ[k] k := by
  let K := dgHomComplex k X X
  let tr : K.X 2 ⟶ ModuleCat.of k k :=
    ModuleCat.ofHom (zigzagAlgebraFiniteTwistedTrace k G c X v hv)
  have ht : K.d 1 2 ≫ tr = 0 := by
    ext f
    exact zigzagAlgebraFiniteTwistedTrace_dgDifferential k G c X v hv hc f
  exact (K.homologyι 2 ≫ K.descOpcycles tr 1 (by simp) ht).hom

/-- On a canonical cycle class, the descended trace evaluates the representing cocycle. -/
@[simp]
theorem zigzagAlgebraFiniteTwistedHomologyTrace_homologyπ (c : V → k)
    (X : DGTwistedObject k (DGAdditiveClosure
      (DGRightModuleCat.{u, u, u}
        (IsDGAlgebra.gradedOpposite (G := Γ) (isDGAlgebra_zero (Γ).piece)))))
    (v : X.obj.ι → V) (hv : ∀ i, X.obj.X i = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i))
    (z : (dgHomComplex k X X).cycles 2) :
    zigzagAlgebraFiniteTwistedHomologyTrace k G c X v hv hc
      (((dgHomComplex k X X).homologyπ 2).hom z) =
      zigzagAlgebraFiniteTwistedTrace k G c X v hv
        (((dgHomComplex k X X).iCycles 2).hom z) := by
  let K := dgHomComplex k X X
  let tr : K.X 2 ⟶ ModuleCat.of k k :=
    ModuleCat.ofHom (zigzagAlgebraFiniteTwistedTrace k G c X v hv)
  have ht : K.d 1 2 ≫ tr = 0 := by
    ext f
    exact zigzagAlgebraFiniteTwistedTrace_dgDifferential k G c X v hv hc f
  have h : K.homologyπ 2 ≫ K.homologyι 2 ≫ K.descOpcycles tr 1 (by simp) ht =
      K.iCycles 2 ≫ tr := by
    rw [HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.p_descOpcycles]
  simpa only [K, tr, zigzagAlgebraFiniteTwistedHomologyTrace, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_ofHom] using
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) z

end TauCeti
