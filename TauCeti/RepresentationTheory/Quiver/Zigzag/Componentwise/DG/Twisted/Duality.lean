/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Algebra.Homology.ShortComplex.PerfectPairing
public import TauCeti.CategoryTheory.DG.GradedHomology
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.TracePairing
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Trace

/-!
# Serre cohomology duality on the formal twisted closure of zigzag projectives

Given a finite simple graph `G` and an object `X` of `TauCeti.ZigzagProjectiveTwistedClosure k G`
equipped with a vertex-projective presentation `(v, hv)`, composing morphisms
`f : DGHom k d X Y` and `g : DGHom k (2 - d) Y X` and evaluating the degree-two supertrace
`TauCeti.ZigzagProjectiveTwistedClosure.trace` defines a bilinear pairing `dgHomPairing` in every
pair of complementary degrees `(d, 2 - d)` against every formal twisted object `Y`.

1. **Chain-level perfectness over any commutative ring:** When the vertex weights `c : V → kˣ` are
   units, `dgHomPairing` decomposes across the formal matrix entries and shift signs into unit
   multiples of `TauCeti.zigzagAlgebraProjectiveDGHomWeightedTracePairing`, hence is a perfect
   pairing (`LinearMap.IsPerfPair`) over any commutative coefficient ring `k` without requiring
   a presentation of `Y` or any edge sign relation.
2. **Cohomology descent and Serre duality:** When `c` assigns opposite weights to adjacent vertices
   occurring in `X`, `trace_dgDifferential` and the graded Leibniz rule make `dgHomPairing`
   compatible with the Maurer–Cartan twisted differentials on `dgHomComplex k X Y` and
   `dgHomComplex k Y X`. Descending via `CochainComplex.homologyPairing` produces `homologyPairing`,
   which agrees with graded cohomology composition `TauCeti.dgHomologyComp` followed by
   `homologyTrace`, and is perfect over every self-injective commutative ring (`Module.Baer k k`)
   and in particular over every field `k`.
3. **All-object 2-Calabi–Yau Serre duality for bipartite graphs:** Any `2`-coloring of a bipartite
   graph `G` supplies unit weights `±1` flipping sign across every edge in every characteristic
   (including characteristic two), yielding an unconditional perfect cohomology pairing
   `bipartiteHomologyPairing` and linear duality `bipartiteHomologyDuality` for all objects
   `X, Y : ZigzagProjectiveTwistedClosure k G` and all degrees `d : ℤ`.

## Main definitions and results

* `TauCeti.ZigzagProjectiveTwistedClosure.dgHomPairing` and
  `TauCeti.ZigzagProjectiveTwistedClosure.dgHomPairing_isPerfPair`: chain-level composition-trace
  perfect pairing over any commutative ring.
* `TauCeti.ZigzagProjectiveTwistedClosure.homologyPairing`,
  `TauCeti.ZigzagProjectiveTwistedClosure.homologyPairing_eq_compr₂_homologyTrace`,
  `TauCeti.ZigzagProjectiveTwistedClosure.isPerfPair_homologyPairing_of_baer`, and
  `TauCeti.ZigzagProjectiveTwistedClosure.isPerfPair_homologyPairing`: cohomology descent and
  perfectness under local edge-sign compatibility.
* `TauCeti.ZigzagProjectiveTwistedClosure.bipartiteHomologyPairing`,
  `TauCeti.ZigzagProjectiveTwistedClosure.isPerfPair_bipartiteHomologyPairing`, and
  `TauCeti.ZigzagProjectiveTwistedClosure.bipartiteHomologyDuality`: all-object 2-Calabi–Yau Serre
  duality for bipartite graphs.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*,
  Sections 2c and 4b.
* B. Keller, *Calabi-Yau triangulated categories*, Section 2.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.ZigzagProjectiveTwistedClosure

universe u

variable (k : Type u) {V : Type u} [Finite V] (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "D" => zigzagAlgebraProjectiveDGRightModule k G
local notation "L" => zigzagAlgebraProjectiveDGHomEquivCorner k G
local notation "E" => zigzagAlgebraProjectiveDGHomEquivCornerOfDegree k G
local notation "𝒱" => DGFullSubcategory (fun M ↦ ∃ i : V, M = D i)
local notation "𝒮" => DGShiftClosure 𝒱

section CommRing

variable [CommRing k]

private def homCongr {M M' N N' : DGRightModuleCat.{u, u, u}
      (IsDGAlgebra.gradedOpposite (G := zigzagAlgebraInternalGrading k G)
        (isDGAlgebra_zero (zigzagAlgebraInternalGrading k G).piece))}
    (hM : M = M') (hN : N = N') (n : ℤ) :
    DGHom k n M N ≃ₗ[k] DGHom k n M' N' :=
  let e := eqToIso (congrArg₂ (fun A B ↦ (dgHomComplex k A B).X n) hM hN)
  { toFun := e.hom.hom
    invFun := e.inv.hom
    left_inv _ := by subst M' N'; rfl
    right_inv _ := by subst M' N'; rfl
    map_add' := map_add _
    map_smul' := map_smul _ }

private theorem eqToIso_hom_apply_eq_homCongr {M M' N N' : DGRightModuleCat.{u, u, u}
      (IsDGAlgebra.gradedOpposite (G := zigzagAlgebraInternalGrading k G)
        (isDGAlgebra_zero (zigzagAlgebraInternalGrading k G).piece))}
    (hM : M = M') (hN : N = N') (n : ℤ) (x : DGHom k n M N) :
    (eqToIso (congrArg₂ (fun A B ↦ (dgHomComplex k A B).X n) hM hN)).hom.hom x =
      homCongr k G hM hN n x :=
  (rfl)

private theorem homCongr_comp {M M' N N' P P' : DGRightModuleCat.{u, u, u}
      (IsDGAlgebra.gradedOpposite (G := zigzagAlgebraInternalGrading k G)
        (isDGAlgebra_zero (zigzagAlgebraInternalGrading k G).piece))}
    (hM : M = M') (hN : N = N') (hP : P = P') {p q n : ℤ}
    (f : DGHom k p M N) (g : DGHom k q N P) (h : p + q = n) :
    homCongr k G hM hP n (dgComp k f g h) =
      dgComp k (homCongr k G hM hN p f) (homCongr k G hN hP q g) h := by
  subst M' N' P'
  rfl

private def piSwap {α β : Type*} (M : α → β → Type*)
    [∀ a b, AddCommMonoid (M a b)] [∀ a b, Module k (M a b)] :
    (∀ b a, M a b) ≃ₗ[k] (∀ a b, M a b) where
  toFun g a b := g b a
  invFun g b a := g a b
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem piSwap_apply {α β : Type*} (M : α → β → Type*)
    [∀ a b, AddCommMonoid (M a b)] [∀ a b, Module k (M a b)]
    (g : ∀ b a, M a b) (a : α) (b : β) :
    piSwap k M g a b = g b a :=
  (rfl)

/-- The chain-level composition-supertrace pairing between complementary degrees `d` and `2 - d`
in `ZigzagProjectiveTwistedClosure k G`, depending on a vertex presentation `(v, hv)` of `X`. -/
def dgHomPairing (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (d : ℤ) :
    DGHom k d X Y →ₗ[k] DGHom k (2 - d) Y X →ₗ[k] k :=
  LinearMap.mk₂ k
    (fun f g ↦ trace k G c X v hv (dgComp k f g (add_sub_cancel d 2)))
    (fun f₁ f₂ g ↦ by rw [add_dgComp, map_add])
    (fun r f g ↦ by rw [smul_dgComp, map_smul])
    (fun f g₁ g₂ ↦ by rw [dgComp_add, map_add])
    (fun r f g ↦ by rw [dgComp_smul, map_smul])

/-- `dgHomPairing` evaluates the degree-two supertrace of `X` on the enriched composite `dgComp`. -/
@[simp]
theorem dgHomPairing_apply (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (d : ℤ)
    (f : DGHom k d X Y) (g : DGHom k (2 - d) Y X) :
    dgHomPairing k G c X Y v hv d f g =
      trace k G c X v hv (dgComp k f g (add_sub_cancel d 2)) :=
  (rfl)

/-- Under opposite weights across edges between the presentations of `X` and `Y`, `dgHomPairing`
satisfies graded symmetry with sign `(-1) ^ (d * (2 - d))`. -/
theorem dgHomPairing_flip (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (w : Y.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j))
    (hc : ∀ i j, G.Adj (v i) (w j) → c (w j) = -c (v i))
    (d : ℤ) (f : DGHom k d X Y) (g : DGHom k (2 - d) Y X) :
    dgHomPairing k G c X Y v hv d f g =
      (d * (2 - d)).negOnePow •
        trace k G c Y w hw (dgComp k g f (sub_add_cancel 2 d)) :=
  trace_comp k G c X Y v w hv hw hc d f g

private def leftEntryEquiv {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j))
    (d : ℤ) (i : X.obj.ι) (j : Y.obj.ι) :
    DGHom k d (X.obj.X i) (Y.obj.X j) ≃ₗ[k]
      DGHom k (d + ((Y.obj.X j).shift - (X.obj.X i).shift)) (D (v i)) (D (w j)) :=
  (DGShiftClosure.dgHomEquiv k (X.obj.X i) (Y.obj.X j) d).trans
    (homCongr k G (hv i) (hw j) (d + ((Y.obj.X j).shift - (X.obj.X i).shift)))

private def rightEntryEquiv {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j))
    (d : ℤ) (i : X.obj.ι) (j : Y.obj.ι) :
    DGHom k (2 - d) (Y.obj.X j) (X.obj.X i) ≃ₗ[k]
      DGHom k (2 - (d + ((Y.obj.X j).shift - (X.obj.X i).shift))) (D (w j)) (D (v i)) :=
  ((DGShiftClosure.dgHomEquiv k (Y.obj.X j) (X.obj.X i) (2 - d)).trans
    (homCongr k G (hw j) (hv i) ((2 - d) + ((X.obj.X i).shift - (Y.obj.X j).shift)))).trans
    ((dgHomComplex k (D (w j)) (D (v i))).XIsoOfEq (by omega)).toLinearEquiv

private theorem entry_comp_eq {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j))
    (d : ℤ) (i : X.obj.ι) (j : Y.obj.ι)
    (f : DGHom k d (X.obj.X i) (Y.obj.X j))
    (g : DGHom k (2 - d) (Y.obj.X j) (X.obj.X i)) :
    castDeg k (by omega)
      (homCongr k G (hv i) (hv i) (2 + ((X.obj.X i).shift - (X.obj.X i).shift))
        (DGShiftClosure.dgHomEquiv k (X.obj.X i) (X.obj.X i) 2
          (dgComp k f g (add_sub_cancel d 2)))) =
      (((X.obj.X i).shift - (Y.obj.X j).shift) *
        (d + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow •
        dgComp k (leftEntryEquiv k G v w hv hw d i j f)
          (rightEntryEquiv k G v w hv hw d i j g) (add_sub_cancel _ 2) := by
  simp only [DGShiftClosure.dgHomEquiv_dgComp, DGFullSubcategory.dgComp_eq, map_zsmul_unit]
  congr 1
  rw [homCongr_comp k G (hv i) (hw j) (hv i)]
  simp only [leftEntryEquiv, rightEntryEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply,
    ← castDeg_def]
  rw [dgComp_castDeg k (by omega) (by omega : 2 + ((X.obj.X i).shift - (X.obj.X i).shift) = 2)]

private def diagTerm (c : V → kˣ) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (i : X.obj.ι) :
    DGHom k 2 (X.obj.X i) (X.obj.X i) →ₗ[k] k :=
  (X.obj.X i).shift.negOnePow • (c (v i) : k) •
    (zigzagAlgebraTrace k G).comp ((Submodule.subtype _).comp
      ((E (v i) (v i) 2).toLinearMap.comp
        ((castDeg k (by omega)).comp
          ((homCongr k G (hv i) (hv i)
            (2 + ((X.obj.X i).shift - (X.obj.X i).shift))).toLinearMap.comp
            (DGShiftClosure.dgHomEquiv k (X.obj.X i) (X.obj.X i) 2).toLinearMap))))

private theorem diagTerm_eq (c : V → kˣ) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (i : X.obj.ι) (z : DGHom k 2 (X.obj.X i) (X.obj.X i)) :
    (X.obj.X i).shift.negOnePow •
      ((c (v i) : k) * zigzagAlgebraTrace k G
        (E (v i) (v i) 2
          (castDeg k (by omega)
            ((eqToIso (congrArg₂
              (fun A B ↦ (dgHomComplex k A B).X
                (2 + ((X.obj.X i).shift - (X.obj.X i).shift)))
              (hv i) (hv i))).hom.hom
              (DGShiftClosure.dgHomEquiv k (X.obj.X i) (X.obj.X i) 2 z))) : Z)) =
      diagTerm k G c X v hv i z :=
  (rfl)

private theorem diagTerm_dgComp (c : V → kˣ) {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j))
    (d : ℤ) (i : X.obj.ι) (j : Y.obj.ι)
    (f : DGHom k d (X.obj.X i) (Y.obj.X j))
    (g : DGHom k (2 - d) (Y.obj.X j) (X.obj.X i)) :
    diagTerm k G c X v hv i (dgComp k f g (add_sub_cancel d 2)) =
      ((X.obj.X i).shift.negOnePow *
        (((X.obj.X i).shift - (Y.obj.X j).shift) *
          (d + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow) •
        zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c (v i) (w j)
          (d + ((Y.obj.X j).shift - (X.obj.X i).shift))
          (leftEntryEquiv k G v w hv hw d i j f)
          (rightEntryEquiv k G v w hv hw d i j g) := by
  dsimp only [diagTerm, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.coe_subtype, smul_eq_mul]
  conv_lhs =>
    rw [entry_comp_eq k G v w hv hw d i j, map_zsmul_unit, Submodule.coe_smul_of_tower,
      map_zsmul_unit, mul_smul_comm, smul_smul,
      coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_apply, castDeg_self]
  exact (congrArg
    (((X.obj.X i).shift.negOnePow *
      (((X.obj.X i).shift - (Y.obj.X j).shift) *
        (d + ((Y.obj.X j).shift - (X.obj.X i).shift))).negOnePow) • ·)
    (zigzagAlgebraProjectiveDGHomWeightedTracePairing_apply k G c (v i) (w j)
      (d + ((Y.obj.X j).shift - (X.obj.X i).shift))
      (leftEntryEquiv k G v w hv hw d i j f)
      (rightEntryEquiv k G v w hv hw d i j g))).symm

/-- Unit vertex weights make `dgHomPairing` a perfect pairing over any commutative coefficient ring
`k`, for arbitrary formal twisted objects `X` and `Y` and every degree `d : ℤ`. -/
instance dgHomPairing_isPerfPair (c : V → kˣ) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (d : ℤ) :
    (dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv d).IsPerfPair := by
  let w : Y.obj.ι → V := fun j ↦ (Y.obj.X j).obj.property.choose
  have hw : ∀ j, (Y.obj.X j).obj.obj = D (w j) := fun j ↦ (Y.obj.X j).obj.property.choose_spec
  let dij (i : X.obj.ι) (j : Y.obj.ι) : ℤ := d + ((Y.obj.X j).shift - (X.obj.X i).shift)
  let sgn (i : X.obj.ι) (j : Y.obj.ι) : ℤˣ :=
    (X.obj.X i).shift.negOnePow * (((X.obj.X i).shift - (Y.obj.X j).shift) * dij i j).negOnePow
  let eL : DGHom k d X Y ≃ₗ[k] ∀ i j, DGHom k (dij i j) (D (v i)) (D (w j)) :=
    ((DGTwistedObject.dgHomEquiv k X Y d).trans
      (DGAdditiveClosure.dgHomEquiv k X.obj Y.obj d)).trans
      (LinearEquiv.piCongrRight fun i ↦
        LinearEquiv.piCongrRight fun j ↦ leftEntryEquiv k G v w hv hw d i j)
  let eR : DGHom k (2 - d) Y X ≃ₗ[k] ∀ i j, DGHom k (2 - dij i j) (D (w j)) (D (v i)) :=
    (((DGTwistedObject.dgHomEquiv k Y X (2 - d)).trans
      (DGAdditiveClosure.dgHomEquiv k Y.obj X.obj (2 - d))).trans (piSwap k _)).trans
      (LinearEquiv.piCongrRight fun i ↦
        LinearEquiv.piCongrRight fun j ↦ rightEntryEquiv k G v w hv hw d i j)
  let P := LinearMap.piPairing fun i : X.obj.ι ↦
    LinearMap.piPairing fun j : Y.obj.ι ↦
      sgn i j • zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c (v i) (w j) (dij i j)
  have hEq : dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv d =
      P.compl₁₂ eL.toLinearMap eR.toLinearMap := by
    apply LinearMap.ext fun f ↦ LinearMap.ext fun g ↦ ?_
    rw [dgHomPairing_apply, trace_apply]
    simp only [P, eL, eR, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
      LinearMap.piPairing_apply, LinearEquiv.piCongrRight_apply, piSwap_apply,
      LinearMap.smul_apply, DGTwistedObject.dgHomEquiv_dgComp,
      DGAdditiveClosure.dgHomEquiv_dgComp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [diagTerm_eq k G c X v hv i, map_sum (diagTerm k G c X v hv i)]
    exact Finset.sum_congr rfl fun j _ ↦ diagTerm_dgComp k G c v w hv hw d i j _ _
  rw [hEq]
  infer_instance

/-! ### Compatibility with twisted differentials and cohomology descent -/

/-- When adjacent vertices in the presentation of `X` carry opposite weights, `dgHomPairing`
satisfies the graded Leibniz rule with respect to the twisted differentials on `dgHomComplex k X Y`
and `dgHomComplex k Y X`. -/
theorem dgHomPairing_d (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁))
    {a a' : ℤ} (ha : a + 1 = a')
    (f : DGHom k a X Y) (g : DGHom k (2 - a') Y X) :
    dgHomPairing k G c X Y v hv a' (((dgHomComplex k X Y).d a a').hom f) g +
      a.negOnePow •
        dgHomPairing k G c X Y v hv a f (((dgHomComplex k Y X).d (2 - a') (2 - a)).hom g) = 0 := by
  have hd := congrArg (trace k G c X v hv)
    (dgHomComplex_d_dgComp k ha (by omega : 2 - a' + 1 = 2 - a) (rfl : (1 : ℤ) + 1 = 2)
      f g (by omega : a + (2 - a') = 1))
  rw [trace_dgDifferential k G c X v hv hc, map_add, map_zsmul_unit] at hd
  exact hd.symm

/-- `homologyTrace` evaluates on `TauCeti.dgHomologyClass` to the chain-level supertrace `trace`. -/
@[simp]
theorem homologyTrace_dgHomologyClass (c : V → k) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i))
    (h : DGHom k 2 X X) (hh : dgDifferential k 2 h = 0) :
    homologyTrace k G c X v hv hc (dgHomologyClass k h hh) = trace k G c X v hv h := by
  let K := dgHomComplex k X X
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 2)).mp inferInstance
    (dgHomologyClass k h hh)
  have hz' := hz
  rw [homologyπ_eq_dgHomologyClass, dgHomologyClass_eq_iff] at hz'
  obtain ⟨b, hb⟩ := hz'
  have hiz : (K.iCycles 2).hom z = ((K.d (2 - 1) 2).hom b) + h := eq_add_of_sub_eq hb.symm
  have hd : (K.d (2 - 1) 2).hom b = dgDifferential k 1 b := rfl
  rw [← hz, homologyTrace_homologyπ, hiz, hd, map_add, trace_dgDifferential k G c X v hv hc,
    zero_add]

/-- The descended cohomology pairing `(dgHomComplex k X Y).homology d →ₗ[k]
(dgHomComplex k Y X).homology (2 - d) →ₗ[k] k` induced by `dgHomPairing`. -/
def homologyPairing (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ) :
    (dgHomComplex k X Y).homology d →ₗ[k]
      (dgHomComplex k Y X).homology (2 - d) →ₗ[k] k :=
  (dgHomComplex k X Y).homologyPairing (dgHomComplex k Y X) 2
    (dgHomPairing k G c X Y v hv)
    (fun ha f g ↦ dgHomPairing_d k G c X Y v hv hc ha f g) d

/-- On `homologyπ` classes of cocycles, `homologyPairing` evaluates `dgHomPairing` on the
underlying cocycles. -/
theorem homologyPairing_homologyπ (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ)
    (x : (dgHomComplex k X Y).cycles d) (y : (dgHomComplex k Y X).cycles (2 - d)) :
    homologyPairing k G c X Y v hv hc d
      (((dgHomComplex k X Y).homologyπ d).hom x)
      (((dgHomComplex k Y X).homologyπ (2 - d)).hom y) =
      dgHomPairing k G c X Y v hv d
        (((dgHomComplex k X Y).iCycles d).hom x)
        (((dgHomComplex k Y X).iCycles (2 - d)).hom y) :=
  CochainComplex.homologyPairing_homologyπ _ _ _ _ _ d x y

/-- `homologyPairing` coincides with graded cohomology composition `TauCeti.dgHomologyComp`
followed by `homologyTrace`. -/
theorem homologyPairing_eq_compr₂_homologyTrace
    (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ) :
    homologyPairing k G c X Y v hv hc d =
      (dgHomologyComp k X Y X (add_sub_cancel d 2)).compr₂ (homologyTrace k G c X v hv hc) := by
  apply LinearMap.ext fun a ↦ LinearMap.ext fun b ↦ ?_
  obtain ⟨x, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((dgHomComplex k X Y).homologyπ d)).mp inferInstance a
  obtain ⟨y, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((dgHomComplex k Y X).homologyπ (2 - d))).mp inferInstance b
  rw [homologyPairing_homologyπ, LinearMap.compr₂_apply,
    homologyπ_eq_dgHomologyClass, homologyπ_eq_dgHomologyClass,
    dgHomologyComp_dgHomologyClass, homologyTrace_dgHomologyClass, dgHomPairing_apply]

/-- On `TauCeti.dgHomologyClass` representatives, `homologyPairing` evaluates `dgHomPairing`. -/
@[simp]
theorem homologyPairing_dgHomologyClass (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ)
    (f : DGHom k d X Y) (g : DGHom k (2 - d) Y X)
    (hf : dgDifferential k d f = 0) (hg : dgDifferential k (2 - d) g = 0) :
    homologyPairing k G c X Y v hv hc d (dgHomologyClass k f hf) (dgHomologyClass k g hg) =
      dgHomPairing k G c X Y v hv d f g := by
  rw [homologyPairing_eq_compr₂_homologyTrace, LinearMap.compr₂_apply,
    dgHomologyComp_dgHomologyClass, homologyTrace_dgHomologyClass, dgHomPairing_apply]

/-- Over a self-injective commutative ring (`Module.Baer k k`), unit vertex weights satisfying the
adjacent sign condition on `X` make `homologyPairing` a perfect pairing in every degree `d : ℤ`. -/
theorem isPerfPair_homologyPairing_of_baer (hk : Module.Baer k k) (c : V → kˣ)
    (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → (c (v i₂) : k) = -(c (v i₁) : k)) (d : ℤ) :
    (homologyPairing k G (fun u ↦ (c u : k)) X Y v hv hc d).IsPerfPair :=
  CochainComplex.isPerfPair_homologyPairing_of_baer
    (dgHomComplex k X Y) (dgHomComplex k Y X) 2 hk
    (dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv)
    (fun ha f g ↦ dgHomPairing_d k G (fun u ↦ (c u : k)) X Y v hv hc ha f g) d

/-! ### Bipartite all-object Serre duality -/

/-- Unit weights `±1` associated to a chosen `2`-coloring of a bipartite graph `G`, flipping sign
across every edge in every characteristic (including characteristic two). -/
def bipartiteWeight (hG : G.IsBipartite) : V → kˣ :=
  fun u ↦ if (hG.some u : ℕ) = 0 then 1 else -1

omit [Finite V] in
/-- Adjacent vertices of a bipartite graph carry opposite `bipartiteWeight` values. -/
theorem bipartiteWeight_adj (hG : G.IsBipartite) {u₁ u₂ : V} (hadj : G.Adj u₁ u₂) :
    (bipartiteWeight k G hG u₂ : k) = -(bipartiteWeight k G hG u₁ : k) := by
  have hne : hG.some u₁ ≠ hG.some u₂ := hG.some.valid hadj
  have hlt₁ : (hG.some u₁ : ℕ) < 2 := (hG.some u₁).isLt
  have hlt₂ : (hG.some u₂ : ℕ) < 2 := (hG.some u₂).isLt
  have hval_ne : (hG.some u₁ : ℕ) ≠ (hG.some u₂ : ℕ) := fun h ↦ hne (Fin.ext h)
  dsimp only [bipartiteWeight]
  by_cases h₁ : (hG.some u₁ : ℕ) = 0
  · have h₂ : (hG.some u₂ : ℕ) ≠ 0 := by omega
    simp only [h₁, h₂, ↓reduceIte, Units.val_one, Units.val_neg]
  · have h₂ : (hG.some u₂ : ℕ) = 0 := by omega
    simp only [h₁, h₂, ↓reduceIte, Units.val_one, Units.val_neg, neg_neg]

/-- All-object cohomology pairing on `ZigzagProjectiveTwistedClosure k G` for a bipartite graph
`G`, requiring no explicit vertex presentation from the caller. -/
def bipartiteHomologyPairing (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (dgHomComplex k X Y).homology d →ₗ[k]
      (dgHomComplex k Y X).homology (2 - d) →ₗ[k] k :=
  homologyPairing k G (fun u ↦ (bipartiteWeight k G hG u : k)) X Y
    (fun i ↦ (X.obj.X i).obj.property.choose)
    (fun i ↦ (X.obj.X i).obj.property.choose_spec)
    (fun _ _ hadj ↦ bipartiteWeight_adj k G hG hadj) d

/-- Over a self-injective commutative ring (`Module.Baer k k`), `bipartiteHomologyPairing` is a
perfect pairing for all formal twisted objects `X, Y` and all degrees `d : ℤ`. -/
theorem isPerfPair_bipartiteHomologyPairing_of_baer (hk : Module.Baer k k) (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (bipartiteHomologyPairing k G hG X Y d).IsPerfPair :=
  isPerfPair_homologyPairing_of_baer k G hk (bipartiteWeight k G hG) X Y _ _ _ d

end CommRing

section Field

variable [Field k]

/-- Over a field `k`, unit vertex weights satisfying the adjacent sign condition on `X` make
`homologyPairing` a perfect pairing in every degree `d : ℤ`. -/
theorem isPerfPair_homologyPairing (c : V → kˣ)
    (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → (c (v i₂) : k) = -(c (v i₁) : k)) (d : ℤ) :
    (homologyPairing k G (fun u ↦ (c u : k)) X Y v hv hc d).IsPerfPair :=
  CochainComplex.isPerfPair_homologyPairing
    (dgHomComplex k X Y) (dgHomComplex k Y X) 2
    (dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv)
    (fun ha f g ↦ dgHomPairing_d k G (fun u ↦ (c u : k)) X Y v hv hc ha f g) d

/-- The Serre duality linear equivalence `Hom^d(X, Y) ≃ₗ[k] Dual(Hom^{2 - d}(Y, X))` induced by a
unit vertex weighting satisfying the adjacent sign condition on `X`. -/
def homologyDuality (c : V → kˣ) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → (c (v i₂) : k) = -(c (v i₁) : k)) (d : ℤ) :
    (dgHomComplex k X Y).homology d ≃ₗ[k]
      Module.Dual k ((dgHomComplex k Y X).homology (2 - d)) :=
  have := isPerfPair_homologyPairing k G c X Y v hv hc d
  (homologyPairing k G (fun u ↦ (c u : k)) X Y v hv hc d).toPerfPair

/-- Over a field `k` and a bipartite graph `G`, `bipartiteHomologyPairing` is a perfect pairing for
all formal twisted objects `X, Y` and all degrees `d : ℤ`. -/
instance isPerfPair_bipartiteHomologyPairing (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (bipartiteHomologyPairing k G hG X Y d).IsPerfPair :=
  isPerfPair_homologyPairing k G (bipartiteWeight k G hG) X Y _ _ _ d

/-- All-object 2-Calabi–Yau Serre duality `Hom^d(X, Y) ≃ₗ[k] Dual(Hom^{2 - d}(Y, X))` on
`ZigzagProjectiveTwistedClosure k G` for a bipartite graph `G` over a field `k`. -/
def bipartiteHomologyDuality (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (dgHomComplex k X Y).homology d ≃ₗ[k]
      Module.Dual k ((dgHomComplex k Y X).homology (2 - d)) :=
  (bipartiteHomologyPairing k G hG X Y d).toPerfPair

end Field

end TauCeti.ZigzagProjectiveTwistedClosure
