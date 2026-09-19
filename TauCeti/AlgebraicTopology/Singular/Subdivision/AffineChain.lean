/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Basic

/-!
# Affine chains in convex spaces

An affine `k`-chain in a convex space `E` is a formal integral combination of `(k + 1)`-tuples of
points of `E`, the vertex tuples of affine `k`-simplices. This file equips affine chains with the
simplicial boundary, the push-forward along maps, the cone from a point and the barycentric
subdivision, and pushes affine chains of the standard simplex `Δᵐ` forward along a singular
`m`-simplex to singular chains with coefficients in an object of a preadditive category.

These are the linear chains of Hatcher's proof of excision: operators on singular chains, such as
the prism operator of barycentric subdivision, are defined on the standard simplex as affine
chains and transported to singular chains along singular simplices.

## Main definitions and results

* `TauCeti.AffineChain.boundary`: the boundary of affine chains, with
  `TauCeti.AffineChain.boundary_boundary`: `∂ ∂ = 0`.
* `TauCeti.AffineChain.map`: the push-forward along a map of vertices.
* `TauCeti.AffineChain.cone`: the cone from a point `b`, with
  `TauCeti.AffineChain.boundary_cone`: `∂ (b · c) = c - b · ∂ c` in positive degrees.
* `TauCeti.AffineChain.subdivision`: the barycentric subdivision, which commutes with the boundary
  (`TauCeti.AffineChain.boundary_subdivision`) and with affine maps
  (`TauCeti.AffineChain.map_subdivision`).
* `TauCeti.AffineChain.singularChain`: the push-forward of affine chains of `Δᵐ` along a singular
  `m`-simplex, compatible with the boundary, faces, subdivision and continuous maps.
* `ContinuousMap.singularChain_subdivision`: pushing forward commutes with subdivision.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, step (1).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial Equiv AlgebraicTopology Finsupp

universe w v u

namespace TauCeti

namespace AffineChain

variable {E F G : Type*}

variable (E) in
/-- The simplicial boundary of formal integral combinations of `(k + 1)`-tuples of vertices: the
alternating sum of the tuples obtained by deleting one vertex. -/
def boundary (k : ℕ) : ((Fin (k + 2) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 1) → E) →₀ ℤ) :=
  linearCombination ℤ fun v ↦ ∑ i : Fin (k + 2), single (v ∘ i.succAbove) ((-1 : ℤ) ^ (i : ℕ))

@[simp]
lemma boundary_single {k : ℕ} (v : Fin (k + 2) → E) (a : ℤ) :
    boundary E k (single v a) =
      ∑ i : Fin (k + 2), single (v ∘ i.succAbove) (a * (-1 : ℤ) ^ (i : ℕ)) := by
  simp [boundary, Finset.smul_sum, smul_single]

private lemma succ_succAbove_comp_succAbove {k : ℕ} {i j : Fin (k + 2)} (h : i ≤ j) :
    j.succ.succAbove ∘ i.succAbove = i.castSucc.succAbove ∘ j.succAbove :=
  congrArg (fun f ↦ ⇑(SimplexCategory.Hom.toOrderHom f))
    (SimplexCategory.δ_comp_δ h)

/-- The boundary of a boundary vanishes. -/
lemma boundary_boundary (k : ℕ) : boundary E k ∘ₗ boundary E (k + 1) = 0 := by
  refine lhom_ext' fun v ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, boundary_single, map_sum,
    LinearMap.zero_apply, one_mul, Function.comp_assoc]
  -- The terms indexed by `(i, j)` with `j < i` cancel against those indexed by `(j, i - 1)`,
  -- by the simplicial identity `succ_succAbove_comp_succAbove`; `g` is this pairing.
  rw [← Finset.sum_product']
  let g : Fin (k + 3) × Fin (k + 2) → Fin (k + 3) × Fin (k + 2) := fun p ↦
    if h : p.2.castSucc < p.1 then (p.2.castSucc, p.1.pred (Fin.ne_zero_of_lt h))
    else (p.2.succ, p.1.castLT (by have := p.2.2; simp [Fin.lt_def] at h; omega))
  have hgg : ∀ p, g (g p) = p := by
    rintro ⟨a, b⟩
    by_cases h : b.castSucc < a
    · have h' : ¬ (a.pred (Fin.ne_zero_of_lt h)).castSucc < b.castSucc := by
        simp [Fin.lt_def] at h ⊢; omega
      simp [g, h, h']
    · have h' : (a.castLT (by have := b.2; simp [Fin.lt_def] at h; omega)).castSucc < b.succ := by
        simp [Fin.lt_def] at h ⊢; omega
      simp only [g, h, h', dite_true, dite_false]
      ext <;> simp
  have key : ∀ p : Fin (k + 3) × Fin (k + 2), p.2.castSucc < p.1 →
      single (v ∘ p.1.succAbove ∘ p.2.succAbove) ((-1 : ℤ) ^ (p.1 : ℕ) * (-1) ^ (p.2 : ℕ)) +
      single (v ∘ (g p).1.succAbove ∘ (g p).2.succAbove)
        ((-1 : ℤ) ^ ((g p).1 : ℕ) * (-1) ^ ((g p).2 : ℕ)) = 0 := by
    rintro ⟨a, b⟩ h
    obtain ⟨a, rfl⟩ := Fin.exists_succ_eq.2 (Fin.ne_zero_of_lt h)
    have hba : b ≤ a := Fin.castSucc_lt_succ_iff.1 h
    simp only [g, h, dite_true, Fin.pred_succ]
    rw [succ_succAbove_comp_succAbove hba, ← single_add, Fin.val_succ,
      Fin.val_castSucc, pow_succ]
    ring_nf
    exact single_zero _
  refine Finset.sum_involution (fun p _ ↦ g p) (fun p _ ↦ ?_) (fun p _ _ ↦ ?_)
    (fun _ _ ↦ Finset.mem_univ _) (fun p _ ↦ hgg p)
  · by_cases h : p.2.castSucc < p.1
    · exact key p h
    · have h' : (g p).2.castSucc < (g p).1 := by
        simp only [g, h, dite_false]; simp [Fin.lt_def] at h ⊢; omega
      have := key (g p) h'
      rw [hgg] at this
      exact (add_comm _ _).trans this
  · intro hp
    by_cases h : p.2.castSucc < p.1
    · have := congrArg Prod.fst hp
      simp only [g, h, dite_true] at this
      exact (this ▸ h).false
    · have := congrArg Prod.fst hp
      simp only [g, h, dite_false] at this
      exact h (this ▸ Fin.castSucc_lt_succ)

/-- The vertex tuples pushed forward along a map `f : E → F`. -/
def map (f : E → F) (k : ℕ) : ((Fin (k + 1) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 1) → F) →₀ ℤ) :=
  lmapDomain ℤ ℤ (f ∘ ·)

@[simp]
lemma map_single (f : E → F) {k : ℕ} (v : Fin (k + 1) → E) (a : ℤ) :
    map f k (single v a) = single (f ∘ v) a := by
  simp [map]

lemma map_comp (g : F → G) (f : E → F) (k : ℕ) : map (g ∘ f) k = map g k ∘ₗ map f k := by
  ext v
  simp [Function.comp_assoc]

@[simp]
lemma map_id (k : ℕ) : map (id : E → E) k = LinearMap.id := by
  ext v
  simp

lemma map_boundary (f : E → F) {k : ℕ} (c : (Fin (k + 2) → E) →₀ ℤ) :
    map f k (boundary E k c) = boundary F k (map f (k + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a => simp [Function.comp_assoc]

/-- The cone from a vertex `b`: the vertex `b` is put in front of every vertex tuple. -/
def cone (b : E) (k : ℕ) : ((Fin (k + 1) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 2) → E) →₀ ℤ) :=
  lmapDomain ℤ ℤ fun v : Fin (k + 1) → E ↦ (Fin.cons b v : Fin (k + 2) → E)

@[simp]
lemma cone_single (b : E) {k : ℕ} (v : Fin (k + 1) → E) (a : ℤ) :
    cone b k (single v a) = single (Fin.cons b v) a := by
  simp [cone]

/-- The boundary of a cone of a chain of positive degree is the chain minus the cone of its
boundary. -/
lemma boundary_cone (b : E) (k : ℕ) (c : (Fin (k + 2) → E) →₀ ℤ) :
    boundary E (k + 1) (cone b (k + 1) c) = c - cone b k (boundary E k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]; abel
  | single v a =>
    have h (j : Fin (k + 2)) : j.removeNth v = v ∘ j.succAbove := funext (j.removeNth_apply v)
    rw [cone_single, boundary_single, Fin.sum_univ_succ, boundary_single]
    simp [pow_succ, sub_eq_add_neg, mul_comm, h]

section Subdivision

variable [ConvexSpace ℝ E] [ConvexSpace ℝ F]

variable (E) in
/-- The barycentric subdivision of chains of vertex tuples in a convex space: the tuple `v` is
replaced by the signed sum, over the permutations `π`, of the vertex tuples of the affine simplices
`StdSimplex.affineMapMk v ∘ BarycentricSubdivision.vertex π`. -/
def subdivision (k : ℕ) : ((Fin (k + 1) → E) →₀ ℤ) →ₗ[ℤ] ((Fin (k + 1) → E) →₀ ℤ) :=
  linearCombination ℤ fun v ↦ ∑ π : Perm (Fin (k + 1)),
    single (StdSimplex.affineMapMk (R := ℝ) v ∘ BarycentricSubdivision.vertex π) (π.sign : ℤ)

@[simp]
lemma subdivision_single {k : ℕ} (v : Fin (k + 1) → E) (a : ℤ) :
    subdivision E k (single v a) = ∑ π : Perm (Fin (k + 1)),
      single (StdSimplex.affineMapMk (R := ℝ) v ∘ BarycentricSubdivision.vertex π)
        (a * π.sign) := by
  simp [subdivision, Finset.smul_sum, smul_single]

/-- The subdivision of `0`-chains is the identity. -/
@[simp]
lemma subdivision_zero : subdivision E 0 = LinearMap.id := by
  have : Subsingleton (Perm (Fin (0 + 1))) :=
    ⟨fun _ _ ↦ Equiv.ext fun _ ↦ Subsingleton.elim (α := Fin 1) _ _⟩
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, subdivision_single,
    LinearMap.id_comp]
  rw [Fintype.sum_subsingleton _ 1, Perm.sign_one, Units.val_one, mul_one]
  have hv : ⇑(StdSimplex.affineMapMk (R := ℝ) v) ∘ BarycentricSubdivision.vertex 1 = v := by
    funext i
    rw [Function.comp_apply, Subsingleton.elim (BarycentricSubdivision.vertex 1 i) (.single i),
      StdSimplex.affineMapMk_single]
  rw [hv]

/-- The subdivision commutes with the boundary. -/
lemma boundary_subdivision (k : ℕ) :
    boundary E k ∘ₗ subdivision E (k + 1) = subdivision E k ∘ₗ boundary E k := by
  refine lhom_ext' fun v ↦ LinearMap.ext_ring ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, lsingle_apply, subdivision_single,
    boundary_single, map_sum, one_mul]
  have h := BarycentricSubdivision.sum_sign_boundary
    (fun w ↦ single (⇑(StdSimplex.affineMapMk (R := ℝ) v) ∘ w) (1 : ℤ))
  have hv (j : Fin (k + 2)) : ⇑(StdSimplex.affineMapMk (R := ℝ) (v ∘ j.succAbove)) =
      ⇑(StdSimplex.affineMapMk (R := ℝ) v) ∘ StdSimplex.map j.succAbove := by
    funext x
    simp [StdSimplex.affineMapMk_apply]
  simp only [Finset.smul_sum, Units.smul_def, smul_single, smul_eq_mul, mul_one] at h
  simp only [hv, Function.comp_assoc]
  exact h

/-- The subdivision is natural under affine maps. -/
lemma map_subdivision (f : ConvexSpace.AffineMap ℝ E F) {k : ℕ} (c : (Fin (k + 1) → E) →₀ ℤ) :
    map f k (subdivision E k c) = subdivision F k (map f k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a => simp [← Function.comp_assoc, ← StdSimplex.comp_affineMapMk]

/-- The vertex tuple of the standard `k`-simplex, as an affine `k`-chain of the standard
`k`-simplex. -/
def simplex (k : ℕ) : (Fin (k + 1) → StdSimplex ℝ (Fin (k + 1))) →₀ ℤ :=
  single StdSimplex.single 1

lemma simplex_def (k : ℕ) : simplex k = single StdSimplex.single 1 := (rfl)

lemma map_affineMapMk_simplex {k : ℕ} (v : Fin (k + 1) → E) :
    map (StdSimplex.affineMapMk (R := ℝ) v) k (simplex k) = single v 1 := by
  rw [simplex, map_single]
  congr 1
  funext i
  simp

end Subdivision

section Singular

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] (R : C)
  {X Y : TopCat.{w}}

/-- The singular chains with coefficients in `R` of the affine chains of `Δᵐ` pushed forward
along a singular simplex `σ : Δᵐ → X`: a vertex tuple `v` is sent to the summand of the singular
simplex `σ ∘ StdSimplex.continuousAffineMapMk v`. -/
def singularChain {m : ℕ} (σ : C(StdSimplex ℝ (Fin (m + 1)), X)) (k : ℕ) :
    ((Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) →ₗ[ℤ]
      (R ⟶ ((TopCat.toSSet.obj X).chainComplex R).X k) :=
  linearCombination ℤ fun v ↦ (TopCat.toSSet.obj X).ιChainComplex
    ((X.toSSetObjEquiv _).symm (σ.comp (StdSimplex.continuousAffineMapMk v)))

variable {R}

@[simp]
lemma singularChain_single {m : ℕ} (σ : C(StdSimplex ℝ (Fin (m + 1)), X)) {k : ℕ}
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) (a : ℤ) :
    singularChain R σ k (single v a) = a • (TopCat.toSSet.obj X).ιChainComplex
      ((X.toSSetObjEquiv _).symm (σ.comp (StdSimplex.continuousAffineMapMk v))) := by
  simp [singularChain]

/-- Pushing affine chains forward along a singular simplex commutes with the boundary. -/
lemma singularChain_boundary {m : ℕ} (σ : C(StdSimplex ℝ (Fin (m + 1)), X)) {k : ℕ}
    (c : (Fin (k + 2) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) :
    singularChain R σ k (boundary _ k c) =
      singularChain R σ (k + 1) c ≫ ((TopCat.toSSet.obj X).chainComplex R).d (k + 1) k := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, Preadditive.add_comp]
  | single v a =>
    simp [Finset.smul_sum, mul_smul, SSet.ιChainComplex_d]

/-- Pushing an affine chain forward along a facet of a singular simplex is pushing its image
under the facet inclusion forward along the singular simplex. -/
lemma singularChain_δ {m : ℕ} (σ : TopCat.toSSet.obj X _⦋m + 1⦌) (j : Fin (m + 2)) {k : ℕ}
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) :
    singularChain R (X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ j σ)) k c =
      singularChain R (X.toSSetObjEquiv _ σ) k (map (StdSimplex.map j.succAbove) k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    simp only [singularChain_single, map_single]
    congr 1
    exact congrArg (TopCat.toSSet.obj X).ιChainComplex
      (TopCat.toSSetObjEquiv_symm_comp_affineMapMk_δ σ v j)

/-- Pushing the standard simplex forward along a singular simplex gives that singular simplex. -/
lemma singularChain_simplex {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    singularChain R (X.toSSetObjEquiv _ σ) n (simplex n) =
      (TopCat.toSSet.obj X).ιChainComplex σ := by
  rw [simplex, singularChain_single, one_smul]
  congr 1
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp [StdSimplex.affineMapMk_apply]

/-- Pushing the subdivision of an affine chain forward along a singular simplex gives the
barycentric subdivision of the pushed-forward chain. -/
lemma _root_.ContinuousMap.singularChain_subdivision {m : ℕ}
    (σ : C(StdSimplex ℝ (Fin (m + 1)), X)) {k : ℕ}
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) :
    singularChain R σ k (subdivision _ k c) =
      singularChain R σ k c ≫ singularSubdivisionX R X k := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd, Preadditive.add_comp]
  | single v a =>
    have hv (π : Perm (Fin (k + 1))) :
        StdSimplex.continuousAffineMapMk (R := ℝ)
            (StdSimplex.affineMapMk (R := ℝ) v ∘ BarycentricSubdivision.vertex π) =
          (StdSimplex.continuousAffineMapMk v).comp
            (StdSimplex.continuousAffineMapMk (BarycentricSubdivision.vertex π)) := by
      ext x : 1
      simp [← StdSimplex.comp_affineMapMk]
    simp [hv, Finset.smul_sum, mul_smul, Units.smul_def, ContinuousMap.comp_assoc]

/-- Pushing the subdivision of the standard simplex forward along a singular simplex gives the
barycentric subdivision of that singular simplex. -/
lemma singularChain_subdivision_simplex {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    singularChain R (X.toSSetObjEquiv _ σ) n (subdivision _ n (simplex n)) =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSubdivisionX R X n := by
  rw [_root_.ContinuousMap.singularChain_subdivision, singularChain_simplex]

/-- Pushing affine chains forward along a singular simplex commutes with continuous maps. -/
lemma singularChain_comp_map {m : ℕ} (σ : C(StdSimplex ℝ (Fin (m + 1)), X)) (f : X ⟶ Y) {k : ℕ}
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ) :
    singularChain R σ k c ≫ (SSet.chainComplexMap (TopCat.toSSet.map f) R).f k =
      singularChain R ((ConcreteCategory.hom f).comp σ) k c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Preadditive.add_comp, hc, hd]
  | single v a => simp [SSet.ι_chainComplexMap_f]

end Singular

end AffineChain

end TauCeti
