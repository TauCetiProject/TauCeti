/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Algebra.Homology.ShortComplex.PerfectPairing
public import TauCeti.LinearAlgebra.PerfectPairing.Pi
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.TracePairing
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise.DG.Twisted.Trace

/-!
# Serre cohomology duality on the formal twisted closure of zigzag projectives

For a finite simple graph `G` and `X : TauCeti.ZigzagProjectiveTwistedClosure k G` with vertex
presentation `(v, hv)`, composing in degrees `(d, 2 - d)` and applying `trace` defines
`dgHomPairing`, which is perfect over any commutative ring `k` for unit weights `c : V → kˣ`
(`dgHomPairing_isPerfPair`). Opposite weights across edges in `X` descend `dgHomPairing` to
`homologyPairing`, perfect over self-injective rings (`Module.Baer k k`) and fields, giving
bipartite all-object 2-Calabi–Yau Serre duality `bipartiteHomologyDuality`.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*, §2, §4.
* B. Keller, *Calabi-Yau triangulated categories*, Section 2.
-/

public section
noncomputable section

open CategoryTheory

namespace TauCeti.ZigzagProjectiveTwistedClosure

universe u

variable (k : Type u) {V : Type u} [Finite V] (G : SimpleGraph V)

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "D" => zigzagAlgebraProjectiveDGRightModule k G

section CommRing

variable [CommRing k]

/-- The chain-level composition-supertrace pairing between complementary degrees `d` and `2 - d`
in `ZigzagProjectiveTwistedClosure k G`, depending on a vertex presentation `(v, hv)` of `X`. -/
def dgHomPairing (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (d : ℤ) :
    DGHom k d X Y →ₗ[k] DGHom k (2 - d) Y X →ₗ[k] k :=
  LinearMap.mk₂ k (fun f g ↦ trace k G c X v hv (dgComp k f g (add_sub_cancel d 2)))
    (fun _ _ _ ↦ by rw [add_dgComp, map_add]) (fun _ _ _ ↦ by rw [smul_dgComp, map_smul])
    (fun _ _ _ ↦ by rw [dgComp_add, map_add]) (fun _ _ _ ↦ by rw [dgComp_smul, map_smul])

/-- `dgHomPairing` evaluates the degree-two supertrace of `X` on the enriched composite `dgComp`. -/
@[simp] theorem dgHomPairing_apply (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (d : ℤ)
    (f : DGHom k d X Y) (g : DGHom k (2 - d) Y X) :
    dgHomPairing k G c X Y v hv d f g = trace k G c X v hv (dgComp k f g (add_sub_cancel d 2)) :=
  (rfl)

/-- Under opposite weights across edges between `X` and `Y`, `dgHomPairing` is graded symmetric. -/
theorem dgHomPairing_flip (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (w : Y.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (hc : ∀ i j, G.Adj (v i) (w j) → c (w j) = -c (v i))
    (d : ℤ) (f : DGHom k d X Y) (g : DGHom k (2 - d) Y X) :
    dgHomPairing k G c X Y v hv d f g =
      (d * (2 - d)).negOnePow • trace k G c Y w hw (dgComp k g f (sub_add_cancel 2 d)) :=
  trace_comp k G c X Y v w hv hw hc d f g

private theorem vertexTrace_dgComp_eq_weightedTracePairing (c : V → kˣ) (i j : V) {p q : ℤ}
    (f : DGHom k p (D i) (D j)) (g : DGHom k q (D j) (D i)) (hpq : p + q = 2) :
    vertexTrace k G (c i : k) i (dgComp k f g hpq) =
      zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c i j p f
        (castDeg k (by omega : q = 2 - p) g) := by
  have hcomp : dgComp k f (castDeg k (by omega : q = 2 - p) g) (add_sub_cancel p 2) =
      dgComp k f g hpq := by
    simpa only [castDeg_self] using
      dgComp_castDeg k (by omega : q = 2 - p) (rfl : (2 : ℤ) = 2) f g (add_sub_cancel p 2)
  rw [zigzagAlgebraProjectiveDGHomWeightedTracePairing_apply, hcomp, vertexTrace_apply,
    coe_zigzagAlgebraProjectiveDGHomEquivCornerOfDegree_apply, castDeg_self]

private def entryDeg (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ)
    (i : X.obj.ι) (j : Y.obj.ι) : ℤ :=
  d + ((Y.obj.X j).shift - (X.obj.X i).shift)

private def entrySign (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ)
    (i : X.obj.ι) (j : Y.obj.ι) : ℤˣ :=
  (X.obj.X i).shift.negOnePow *
    (((X.obj.X i).shift - (Y.obj.X j).shift) * entryDeg k G X Y d i j).negOnePow

private def leftHomMatrixEquiv {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (d : ℤ) :
    DGHom k d X Y ≃ₗ[k] ∀ i j, DGHom k (entryDeg k G X Y d i j) (D (v i)) (D (w j)) :=
  ((DGTwistedObject.dgHomEquiv k X Y d).trans
    (DGAdditiveClosure.dgHomEquiv k X.obj Y.obj d)).trans
    (LinearEquiv.piCongrRight fun i ↦ LinearEquiv.piCongrRight fun j ↦
      entryHomEquiv k G (X.obj.X i) (Y.obj.X j) (v i) (w j) (hv i) (hw j) d)

private def rightEntryEquiv {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (d : ℤ) (i : X.obj.ι) (j : Y.obj.ι) :
    DGHom k (2 - d) (Y.obj.X j) (X.obj.X i) ≃ₗ[k]
      DGHom k (2 - entryDeg k G X Y d i j) (D (w j)) (D (v i)) :=
  (entryHomEquiv k G (Y.obj.X j) (X.obj.X i) (w j) (v i) (hw j) (hv i) (2 - d)).trans
    ((dgHomComplex k (D (w j)) (D (v i))).XIsoOfEq (by dsimp [entryDeg]; omega)).toLinearEquiv

private def rightHomMatrixEquiv {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (d : ℤ) :
    DGHom k (2 - d) Y X ≃ₗ[k] ∀ i j, DGHom k (2 - entryDeg k G X Y d i j) (D (w j)) (D (v i)) :=
  (((DGTwistedObject.dgHomEquiv k Y X (2 - d)).trans
    (DGAdditiveClosure.dgHomEquiv k Y.obj X.obj (2 - d))).trans (LinearEquiv.piComm k _)).trans
    (LinearEquiv.piCongrRight fun i ↦
      LinearEquiv.piCongrRight fun j ↦ rightEntryEquiv k G v w hv hw d i j)

private theorem leftHomMatrixEquiv_apply {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (d : ℤ) (f : DGHom k d X Y)
    (i : X.obj.ι) (j : Y.obj.ι) :
    leftHomMatrixEquiv k G v w hv hw d f i j =
      entryHomEquiv k G (X.obj.X i) (Y.obj.X j) (v i) (w j) (hv i) (hw j) d
        (DGAdditiveClosure.dgHomEquiv k X.obj Y.obj d
          (DGTwistedObject.dgHomEquiv k X Y d f) i j) :=
  (rfl)

private theorem rightHomMatrixEquiv_apply {X Y : ZigzagProjectiveTwistedClosure k G}
    (v : X.obj.ι → V) (w : Y.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (d : ℤ) (g : DGHom k (2 - d) Y X)
    (i : X.obj.ι) (j : Y.obj.ι) :
    rightHomMatrixEquiv k G v w hv hw d g i j =
      castDeg k (by dsimp [entryDeg]; omega)
        (entryHomEquiv k G (Y.obj.X j) (X.obj.X i) (w j) (v i) (hw j) (hv i) (2 - d)
          (DGAdditiveClosure.dgHomEquiv k Y.obj X.obj (2 - d)
            (DGTwistedObject.dgHomEquiv k Y X (2 - d) g) j i)) := by
  simp only [rightHomMatrixEquiv, rightEntryEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, LinearEquiv.piComm_apply, Iso.toLinearEquiv_apply,
    ← castDeg_def]

/-- Entrywise decomposition of `dgHomPairing` as a signed `LinearMap.piPairing` of vertex
`zigzagAlgebraProjectiveDGHomWeightedTracePairing`s along `leftHomMatrixEquiv` and
`rightHomMatrixEquiv`. -/
private theorem dgHomPairing_eq_piPairing (c : V → kˣ) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (w : Y.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hw : ∀ j, (Y.obj.X j).obj.obj = D (w j)) (d : ℤ) :
    dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv d =
      (LinearMap.piPairing fun i : X.obj.ι ↦ LinearMap.piPairing fun j : Y.obj.ι ↦
        entrySign k G X Y d i j •
          zigzagAlgebraProjectiveDGHomWeightedTracePairing k G c (v i) (w j)
            (entryDeg k G X Y d i j)).compl₁₂
        (leftHomMatrixEquiv k G v w hv hw d).toLinearMap
        (rightHomMatrixEquiv k G v w hv hw d).toLinearMap := by
  ext f g
  rw [dgHomPairing_apply, trace_eq_sum_shiftedVertexTrace]
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearMap.piPairing_apply,
    LinearMap.smul_apply, DGTwistedObject.dgHomEquiv_dgComp, DGAdditiveClosure.dgHomEquiv_dgComp,
    map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [shiftedVertexTrace_apply, diagonalHomEquiv_comp k G (X.obj.X i) (Y.obj.X j) (v i) (w j)
      (hv i) (hw j) _ _ (add_sub_cancel d 2), map_zsmul_unit,
    vertexTrace_dgComp_eq_weightedTracePairing, smul_smul, leftHomMatrixEquiv_apply,
    rightHomMatrixEquiv_apply]
  rfl

/-- Unit vertex weights make `dgHomPairing` a perfect pairing over any commutative ring `k`. -/
instance dgHomPairing_isPerfPair (c : V → kˣ) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i)) (d : ℤ) :
    (dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv d).IsPerfPair := by
  let w : Y.obj.ι → V := fun j ↦ (Y.obj.X j).obj.property.choose
  have hw : ∀ j, (Y.obj.X j).obj.obj = D (w j) := fun j ↦ (Y.obj.X j).obj.property.choose_spec
  rw [dgHomPairing_eq_piPairing k G c X Y v w hv hw d]
  infer_instance

/-- Under opposite weights across edges in `X`, `dgHomPairing` satisfies the graded Leibniz rule. -/
theorem dgHomPairing_d (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) {a a' : ℤ} (ha : a + 1 = a')
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
@[simp] theorem homologyTrace_dgHomologyClass (c : V → k) (X : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i j, G.Adj (v i) (v j) → c (v j) = -c (v i))
    (h : DGHom k 2 X X) (hh : dgDifferential k 2 h = 0) :
    homologyTrace k G c X v hv hc (dgHomologyClass k h hh) = trace k G c X v hv h := by
  let K := dgHomComplex k X X
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ 2)).mp inferInstance
    (dgHomologyClass k h hh)
  obtain ⟨b, hb⟩ := (dgHomologyClass_eq_iff k _ hh).mp
    ((homologyπ_eq_dgHomologyClass k z).symm.trans hz)
  rw [← hz, homologyTrace_homologyπ, eq_add_of_sub_eq hb.symm, map_add]
  exact (congrArg (· + _) (trace_dgDifferential k G c X v hv hc b)).trans (zero_add _)

/-- The descended cohomology pairing induced by `dgHomPairing`. -/
def homologyPairing (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ) :
    (dgHomComplex k X Y).homology d →ₗ[k] (dgHomComplex k Y X).homology (2 - d) →ₗ[k] k :=
  (dgHomComplex k X Y).homologyPairing (dgHomComplex k Y X) 2 (dgHomPairing k G c X Y v hv)
    (fun ha f g ↦ dgHomPairing_d k G c X Y v hv hc ha f g) d

/-- On `homologyπ` classes of cocycles, `homologyPairing` evaluates `dgHomPairing`. -/
theorem homologyPairing_homologyπ (c : V → k) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ)
    (x : (dgHomComplex k X Y).cycles d) (y : (dgHomComplex k Y X).cycles (2 - d)) :
    homologyPairing k G c X Y v hv hc d (((dgHomComplex k X Y).homologyπ d).hom x)
        (((dgHomComplex k Y X).homologyπ (2 - d)).hom y) =
      dgHomPairing k G c X Y v hv d (((dgHomComplex k X Y).iCycles d).hom x)
        (((dgHomComplex k Y X).iCycles (2 - d)).hom y) :=
  CochainComplex.homologyPairing_homologyπ _ _ _ _ _ d x y

/-- `homologyPairing` coincides with `TauCeti.dgHomologyComp` followed by `homologyTrace`. -/
theorem homologyPairing_eq_compr₂_homologyTrace (c : V → k)
    (X Y : ZigzagProjectiveTwistedClosure k G) (v : X.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ) :
    homologyPairing k G c X Y v hv hc d =
      (dgHomologyComp k X Y X (add_sub_cancel d 2)).compr₂ (homologyTrace k G c X v hv hc) := by
  ext a b
  obtain ⟨x, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((dgHomComplex k X Y).homologyπ d)).mp inferInstance a
  obtain ⟨y, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((dgHomComplex k Y X).homologyπ (2 - d))).mp inferInstance b
  rw [homologyPairing_homologyπ, LinearMap.compr₂_apply, homologyπ_eq_dgHomologyClass,
    homologyπ_eq_dgHomologyClass, dgHomologyComp_dgHomologyClass, homologyTrace_dgHomologyClass,
    dgHomPairing_apply]

/-- On `TauCeti.dgHomologyClass` representatives, `homologyPairing` evaluates `dgHomPairing`. -/
@[simp] theorem homologyPairing_dgHomologyClass (c : V → k)
    (X Y : ZigzagProjectiveTwistedClosure k G) (v : X.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → c (v i₂) = -c (v i₁)) (d : ℤ)
    (f : DGHom k d X Y) (g : DGHom k (2 - d) Y X)
    (hf : dgDifferential k d f = 0) (hg : dgDifferential k (2 - d) g = 0) :
    homologyPairing k G c X Y v hv hc d (dgHomologyClass k f hf) (dgHomologyClass k g hg) =
      dgHomPairing k G c X Y v hv d f g := by
  rw [homologyPairing_eq_compr₂_homologyTrace, LinearMap.compr₂_apply,
    dgHomologyComp_dgHomologyClass, homologyTrace_dgHomologyClass, dgHomPairing_apply]

/-- Over a self-injective commutative ring (`Module.Baer k k`), unit vertex weights satisfying the
adjacent sign condition on `X` make `homologyPairing` perfect in every degree `d : ℤ`. -/
theorem isPerfPair_homologyPairing_of_baer (hk : Module.Baer k k) (c : V → kˣ)
    (X Y : ZigzagProjectiveTwistedClosure k G) (v : X.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → (c (v i₂) : k) = -(c (v i₁) : k)) (d : ℤ) :
    (homologyPairing k G (fun u ↦ (c u : k)) X Y v hv hc d).IsPerfPair :=
  CochainComplex.isPerfPair_homologyPairing_of_baer (dgHomComplex k X Y) (dgHomComplex k Y X) 2 hk
    (dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv)
    (fun ha f g ↦ dgHomPairing_d k G (fun u ↦ (c u : k)) X Y v hv hc ha f g) d

/-- The Serre duality linear equivalence `Hom^d(X, Y) ≃ₗ[k] Dual(Hom^{2 - d}(Y, X))` over a
self-injective commutative ring (`Module.Baer k k`). -/
def homologyDuality (hk : Module.Baer k k) (c : V → kˣ) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → (c (v i₂) : k) = -(c (v i₁) : k)) (d : ℤ) :
    (dgHomComplex k X Y).homology d ≃ₗ[k] Module.Dual k ((dgHomComplex k Y X).homology (2 - d)) :=
  have := isPerfPair_homologyPairing_of_baer k G hk c X Y v hv hc d
  (homologyPairing k G (fun u ↦ (c u : k)) X Y v hv hc d).toPerfPair

/-- `homologyDuality` evaluates at cohomology classes `a` and `b` via `homologyPairing`. -/
@[simp] theorem homologyDuality_apply (hk : Module.Baer k k) (c : V → kˣ)
    (X Y : ZigzagProjectiveTwistedClosure k G) (v : X.obj.ι → V)
    (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → (c (v i₂) : k) = -(c (v i₁) : k)) (d : ℤ)
    (a : (dgHomComplex k X Y).homology d) (b : (dgHomComplex k Y X).homology (2 - d)) :
    homologyDuality k G hk c X Y v hv hc d a b =
      homologyPairing k G (fun u ↦ (c u : k)) X Y v hv hc d a b := (rfl)

/-- Unit weights `±1` associated to a chosen `2`-coloring of a bipartite graph `G`. -/
def bipartiteWeight (hG : G.IsBipartite) : V → kˣ := fun u ↦ if (hG.some u : ℕ) = 0 then 1 else -1

omit [Finite V] in
/-- Adjacent vertices of a bipartite graph carry opposite `bipartiteWeight` values. -/
theorem bipartiteWeight_adj (hG : G.IsBipartite) {u₁ u₂ : V} (hadj : G.Adj u₁ u₂) :
    (bipartiteWeight k G hG u₂ : k) = -(bipartiteWeight k G hG u₁ : k) := by
  have hne : (hG.some u₁ : ℕ) ≠ (hG.some u₂ : ℕ) := fun h ↦ hG.some.valid hadj (Fin.ext h)
  have hlt₁ := (hG.some u₁).isLt; have hlt₂ := (hG.some u₂).isLt; dsimp only [bipartiteWeight]
  by_cases h₁ : (hG.some u₁ : ℕ) = 0
  · simp [h₁, show (hG.some u₂ : ℕ) ≠ 0 by omega]
  · simp [h₁, show (hG.some u₂ : ℕ) = 0 by omega]

/-- All-object cohomology pairing on `ZigzagProjectiveTwistedClosure k G` for a bipartite graph. -/
def bipartiteHomologyPairing (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (dgHomComplex k X Y).homology d →ₗ[k] (dgHomComplex k Y X).homology (2 - d) →ₗ[k] k :=
  homologyPairing k G (fun u ↦ (bipartiteWeight k G hG u : k)) X Y
    (fun i ↦ (X.obj.X i).obj.property.choose) (fun i ↦ (X.obj.X i).obj.property.choose_spec)
    (fun _ _ hadj ↦ bipartiteWeight_adj k G hG hadj) d

/-- Over a self-injective commutative ring, `bipartiteHomologyPairing` is perfect for all `X, Y`. -/
theorem isPerfPair_bipartiteHomologyPairing_of_baer (hk : Module.Baer k k) (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (bipartiteHomologyPairing k G hG X Y d).IsPerfPair :=
  isPerfPair_homologyPairing_of_baer k G hk (bipartiteWeight k G hG) X Y _ _ _ d

/-- All-object 2-Calabi–Yau Serre duality `Hom^d(X, Y) ≃ₗ[k] Dual(Hom^{2 - d}(Y, X))` for a
bipartite graph `G` over a self-injective commutative ring (`Module.Baer k k`). -/
def bipartiteHomologyDuality (hk : Module.Baer k k) (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (dgHomComplex k X Y).homology d ≃ₗ[k] Module.Dual k ((dgHomComplex k Y X).homology (2 - d)) :=
  have := isPerfPair_bipartiteHomologyPairing_of_baer k G hk hG X Y d
  (bipartiteHomologyPairing k G hG X Y d).toPerfPair

/-- `bipartiteHomologyDuality` evaluates at `a` and `b` via `bipartiteHomologyPairing`. -/
@[simp] theorem bipartiteHomologyDuality_apply (hk : Module.Baer k k) (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ)
    (a : (dgHomComplex k X Y).homology d) (b : (dgHomComplex k Y X).homology (2 - d)) :
    bipartiteHomologyDuality k G hk hG X Y d a b = bipartiteHomologyPairing k G hG X Y d a b :=
  (rfl)

end CommRing

section Field

variable [Field k]

/-- Over a field `k`, unit vertex weights satisfying the adjacent sign condition on `X` make
`homologyPairing` a perfect pairing in every degree `d : ℤ`. -/
theorem isPerfPair_homologyPairing (c : V → kˣ) (X Y : ZigzagProjectiveTwistedClosure k G)
    (v : X.obj.ι → V) (hv : ∀ i, (X.obj.X i).obj.obj = D (v i))
    (hc : ∀ i₁ i₂, G.Adj (v i₁) (v i₂) → (c (v i₂) : k) = -(c (v i₁) : k)) (d : ℤ) :
    (homologyPairing k G (fun u ↦ (c u : k)) X Y v hv hc d).IsPerfPair :=
  CochainComplex.isPerfPair_homologyPairing (dgHomComplex k X Y) (dgHomComplex k Y X) 2
    (dgHomPairing k G (fun u ↦ (c u : k)) X Y v hv)
    (fun ha f g ↦ dgHomPairing_d k G (fun u ↦ (c u : k)) X Y v hv hc ha f g) d

/-- Over a field `k` and a bipartite graph `G`, `bipartiteHomologyPairing` is perfect. -/
instance isPerfPair_bipartiteHomologyPairing (hG : G.IsBipartite)
    (X Y : ZigzagProjectiveTwistedClosure k G) (d : ℤ) :
    (bipartiteHomologyPairing k G hG X Y d).IsPerfPair :=
  isPerfPair_homologyPairing k G (bipartiteWeight k G hG) X Y _ _ _ d

end Field

end TauCeti.ZigzagProjectiveTwistedClosure
