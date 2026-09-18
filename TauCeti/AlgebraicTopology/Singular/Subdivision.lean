/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.Geometry.Convex.ConvexSpace.Barycenter
public import TauCeti.Geometry.Convex.ConvexSpace.Topology
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Barycentric subdivision of singular chains

The barycentric subdivision of the standard `n`-simplex `Δⁿ` has one `n`-simplex for each
permutation `π` of the vertices `{0, …, n}`: the affine simplex
`StdSimplex.continuousAffineMapMk (BarycentricSubdivision.vertex π)` whose `k`-th vertex is the
barycenter of the face of `Δⁿ` spanned by `π k, …, π n`. Its vertices are thus the barycenters
of a decreasing chain of faces, starting at the barycenter of `Δⁿ` itself.

The barycentric subdivision of a singular `n`-simplex `σ : Δⁿ → X` is the signed sum over `π` of
`sign π • σ ∘ StdSimplex.continuousAffineMapMk (vertex π)`. This is the closed form of Hatcher's
inductive definition `S σ = σ_♯ (b · S (∂ Δⁿ))`, where `b ·` is the cone from the barycenter `b`
of `Δⁿ`, placed as the first vertex. It is a morphism of singular chain complexes, natural in the
space.

## Main definitions and results

* `TauCeti.BarycentricSubdivision.sum_sign_boundary`: the boundary formula for the subdivision
  of the standard simplex. The faces of the subdivision simplices that meet the interior of `Δⁿ`
  cancel in pairs (exchanging two consecutive entries of `π`), and the remaining faces, which omit
  the barycenter of `Δⁿ`, are the subdivision simplices of the facets of `Δⁿ`, with the signs of
  the simplicial boundary (reindexing through Mathlib's `Equiv.Perm.decomposeFin'`).
* `TauCeti.singularSubdivisionX`: the subdivision of singular `n`-chains with coefficients in an
  object `R` of a preadditive category, computed on summands by
  `TauCeti.ιChainComplex_singularSubdivisionX`; it is the identity on `0`-chains
  (`TauCeti.singularSubdivisionX_zero`).
* `TauCeti.singularSubdivisionChainMap`: the subdivision is a chain map, `∂ S = S ∂`.
* `TauCeti.singularSubdivision`: the subdivision as a natural endomorphism of the singular chain
  complex functor `TopCat ⥤ ChainComplex C ℕ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, steps (2) and (3).
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial Equiv AlgebraicTopology

universe w v u

namespace TauCeti

namespace BarycentricSubdivision

variable {n : ℕ}

/-- The `k`-th vertex of the simplex of the barycentric subdivision of the standard `n`-simplex
indexed by the permutation `π`: the barycenter of the face spanned by `π k, …, π n`. -/
def vertex (π : Perm (Fin (n + 1))) (k : Fin (n + 1)) : StdSimplex ℝ (Fin (n + 1)) :=
  StdSimplex.subBarycenter ((Finset.Ici k).map π.toEmbedding) Finset.nonempty_Ici.map

private lemma subBarycenter_congr {S T : Finset (Fin (n + 1))} (h : S = T) (hS : S.Nonempty) :
    StdSimplex.subBarycenter (K := ℝ) S hS = StdSimplex.subBarycenter T (h ▸ hS) := by
  subst h
  rfl

/-- The vertices of a subdivision simplex other than the barycenter of the simplex are the
vertices of the subdivision simplex of a facet, pushed forward along the facet inclusion. -/
lemma vertex_decomposeFin'Symm_succ (j : Fin (n + 2)) (π : Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    vertex (Perm.decomposeFin'Symm j π) k.succ = (vertex π k).map j.succAbove := by
  rw [vertex, vertex, ← Fin.coe_succAboveEmb, StdSimplex.map_subBarycenter]
  apply subBarycenter_congr
  rw [← Fin.map_succEmb_Ici, Finset.map_map, Finset.map_map]
  congr 1

/-- Exchanging the entries `k` and `k + 1` of `π` does not change the vertices of the
subdivision simplex other than the `(k + 1)`-st one. -/
lemma vertex_mul_swap (π : Perm (Fin (n + 2))) (k : Fin (n + 1)) {t : Fin (n + 2)}
    (ht : t ≠ k.succ) :
    vertex (π * swap k.castSucc k.succ) t = vertex π t := by
  rw [vertex, vertex]
  apply subBarycenter_congr
  rw [Perm.mul_def, Equiv.trans_toEmbedding, ← Finset.map_map]
  congr 1
  ext i
  simp only [Finset.mem_map_equiv, Finset.mem_Ici, symm_swap]
  rcases eq_or_ne i k.castSucc with rfl | h₁
  · rw [swap_apply_left]
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
    have := Fin.val_ne_of_ne ht
    simp only [Fin.val_succ] at this
    omega
  rcases eq_or_ne i k.succ with rfl | h₂
  · rw [swap_apply_right]
    simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
    have := Fin.val_ne_of_ne ht
    simp only [Fin.val_succ] at this
    omega
  · rw [swap_apply_of_ne_of_ne h₁ h₂]

variable {A : Type*} [AddCommGroup A]

/-- The faces of the subdivision simplices of `Δⁿ⁺¹` which contain the barycenter of `Δⁿ⁺¹`
cancel in pairs. -/
lemma sum_sign_face_succ_eq_zero (F : (Fin (n + 1) → StdSimplex ℝ (Fin (n + 2))) → A)
    (k : Fin (n + 1)) :
    ∑ π : Perm (Fin (n + 2)), π.sign • F (vertex π ∘ k.succ.succAbove) = 0 := by
  refine Finset.sum_involution (fun π _ ↦ π * swap k.castSucc k.succ) (fun π _ ↦ ?_)
    (fun π _ _ ↦ ?_) (fun _ _ ↦ Finset.mem_univ _) (fun π _ ↦ by simp [mul_assoc])
  · have hv : vertex (π * swap k.castSucc k.succ) ∘ k.succ.succAbove =
        vertex π ∘ k.succ.succAbove := by
      funext i
      exact vertex_mul_swap π k (Fin.succAbove_ne _ _)
    rw [hv, Perm.sign_mul, Perm.sign_swap k.castSucc_lt_succ.ne]
    simp
  · rw [Ne, mul_eq_left, swap_eq_one_iff]
    exact k.castSucc_lt_succ.ne

/-- The faces of the subdivision simplices of `Δⁿ⁺¹` which omit the barycenter of `Δⁿ⁺¹` are the
subdivision simplices of the facets of `Δⁿ⁺¹`, with the signs of the simplicial boundary. -/
lemma sum_sign_face_zero (F : (Fin (n + 1) → StdSimplex ℝ (Fin (n + 2))) → A) :
    ∑ π : Perm (Fin (n + 2)), π.sign • F (vertex π ∘ Fin.succ) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        ∑ π : Perm (Fin (n + 1)), π.sign • F (StdSimplex.map j.succAbove ∘ vertex π) := by
  rw [← Perm.decomposeFin'.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun π _ ↦ ?_
  have hv : vertex (Perm.decomposeFin'Symm j π) ∘ Fin.succ =
      StdSimplex.map j.succAbove ∘ vertex π :=
    funext (vertex_decomposeFin'Symm_succ j π)
  rw [Perm.decomposeFin'_symm, hv, Perm.sign_decomposeFin'Symm, mul_smul]
  simp [Units.smul_def]

/-- **Boundary formula for the barycentric subdivision of the standard simplex.** The signed
sum of the faces of the subdivision simplices of `Δⁿ⁺¹` equals the signed sum, over the facets of
`Δⁿ⁺¹`, of the subdivision simplices of the facet. The simplices are recorded by their vertices,
and `F` is an arbitrary function of the vertices with values in an abelian group. -/
theorem sum_sign_boundary (F : (Fin (n + 1) → StdSimplex ℝ (Fin (n + 2))) → A) :
    ∑ π : Perm (Fin (n + 2)), π.sign •
        ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) • F (vertex π ∘ k.succAbove) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        ∑ π : Perm (Fin (n + 1)), π.sign • F (StdSimplex.map j.succAbove ∘ vertex π) := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm, Fin.sum_univ_succ]
  have h (k : Fin (n + 1)) : ∑ π : Perm (Fin (n + 2)),
      π.sign • ((-1 : ℤ) ^ (k.succ : ℕ)) • F (vertex π ∘ k.succ.succAbove) = 0 := by
    simp_rw [smul_comm (Perm.sign _) ((-1 : ℤ) ^ (k.succ : ℕ))]
    rw [← Finset.smul_sum, sum_sign_face_succ_eq_zero, smul_zero]
  simp only [h, Finset.sum_const_zero, add_zero, Fin.succAbove_zero, Fin.val_zero, pow_zero,
    one_smul]
  rw [sum_sign_face_zero]
  simp_rw [Finset.smul_sum]

end BarycentricSubdivision

open BarycentricSubdivision

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

section

variable {X : TopCat.{w}}

/-- Precomposing a singular simplex with the affine simplex with vertices `v`, and then with
the inclusion of a facet, is precomposing it with the affine simplex with the restricted vertices.
-/
private lemma δ_toSSetObjEquiv_symm_comp_affineMapMk {m n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (m + 1)), X)) (v : Fin (n + 2) → StdSimplex ℝ (Fin (m + 1)))
    (k : Fin (n + 2)) :
    (TopCat.toSSet.obj X).δ k ((X.toSSetObjEquiv _).symm
        (σ.comp (StdSimplex.continuousAffineMapMk v))) =
      (X.toSSetObjEquiv _).symm (σ.comp (StdSimplex.continuousAffineMapMk (v ∘ k.succAbove))) := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp [StdSimplex.affineMapMk_apply]

/-- Precomposing a facet of a singular simplex with the affine simplex with vertices `v` is
precomposing the singular simplex with the affine simplex with the pushed-forward vertices. -/
private lemma toSSetObjEquiv_symm_comp_affineMapMk_δ {m n : ℕ} (σ : TopCat.toSSet.obj X _⦋m + 1⦌)
    (v : Fin (n + 1) → StdSimplex ℝ (Fin (m + 1))) (j : Fin (m + 2)) :
    (X.toSSetObjEquiv (.op ⦋n⦌)).symm ((X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ j σ)).comp
        (StdSimplex.continuousAffineMapMk v)) =
      (X.toSSetObjEquiv (.op ⦋n⦌)).symm ((X.toSSetObjEquiv _ σ).comp
        (StdSimplex.continuousAffineMapMk (StdSimplex.map j.succAbove ∘ v))) := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  have h := congr($(StdSimplex.comp_affineMapMk (R := ℝ) (StdSimplex.affineMap j.succAbove) v) z)
  simp only [ConvexSpace.AffineMap.coe_comp, Function.comp_apply,
    StdSimplex.coe_affineMap] at h
  simp [h]

end

variable (R : C) (X : TopCat.{w})

/-- The barycentric subdivision of singular `n`-chains of `X` with coefficients in `R`: the
summand of a singular simplex `σ` is sent to the signed sum over the permutations `π` of the
summands of the singular simplices `σ ∘ StdSimplex.continuousAffineMapMk (vertex π)`. -/
def singularSubdivisionX (n : ℕ) :
    ((TopCat.toSSet.obj X).chainComplex R).X n ⟶ ((TopCat.toSSet.obj X).chainComplex R).X n :=
  Cofan.IsColimit.desc ((TopCat.toSSet.obj X).isColimitChainComplexXCofan R n) fun σ ↦
    ∑ π : Perm (Fin (n + 1)), π.sign • (TopCat.toSSet.obj X).ιChainComplex
      ((X.toSSetObjEquiv _).symm
        ((X.toSSetObjEquiv _ σ).comp (StdSimplex.continuousAffineMapMk (vertex π))))

variable {R X} in
@[reassoc (attr := simp)]
lemma ιChainComplex_singularSubdivisionX {n : ℕ} (σ : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ singularSubdivisionX R X n =
      ∑ π : Perm (Fin (n + 1)), π.sign • (TopCat.toSSet.obj X).ιChainComplex
        ((X.toSSetObjEquiv _).symm
          ((X.toSSetObjEquiv _ σ).comp (StdSimplex.continuousAffineMapMk (vertex π)))) :=
  Cofan.IsColimit.fac _ _ σ

/-- The barycentric subdivision is the identity on singular `0`-chains. -/
@[simp]
lemma singularSubdivisionX_zero : singularSubdivisionX R X 0 = 𝟙 _ := by
  ext σ
  have : Subsingleton (Perm (Fin (0 + 1))) :=
    ⟨fun _ _ ↦ Equiv.ext fun _ ↦ Subsingleton.elim (α := Fin 1) _ _⟩
  rw [ιChainComplex_singularSubdivisionX, Fintype.sum_subsingleton _ 1, Category.comp_id,
    Perm.sign_one, one_smul]
  congr 1
  apply (X.toSSetObjEquiv _).injective
  ext z
  simp only [Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  congr 1
  subsingleton

/-- The barycentric subdivision of singular chains of `X` with coefficients in `R`, as an
endomorphism of the singular chain complex: the boundary formula `∂ S = S ∂`. -/
def singularSubdivisionChainMap :
    (TopCat.toSSet.obj X).chainComplex R ⟶ (TopCat.toSSet.obj X).chainComplex R where
  f n := singularSubdivisionX R X n
  comm' := by
    rintro _ n rfl
    ext σ
    simp only [ιChainComplex_singularSubdivisionX_assoc, SSet.ιChainComplex_d_assoc,
      SSet.ιChainComplex_d, Preadditive.sum_comp, Units.smul_def, Preadditive.zsmul_comp,
      ιChainComplex_singularSubdivisionX, δ_toSSetObjEquiv_symm_comp_affineMapMk,
      toSSetObjEquiv_symm_comp_affineMapMk_δ]
    simp only [← Units.smul_def]
    exact sum_sign_boundary fun v ↦ (TopCat.toSSet.obj X).ιChainComplex
      ((X.toSSetObjEquiv _).symm
        ((X.toSSetObjEquiv _ σ).comp (StdSimplex.continuousAffineMapMk v)))

@[simp]
lemma singularSubdivisionChainMap_f (n : ℕ) :
    (singularSubdivisionChainMap R X).f n = singularSubdivisionX R X n := (rfl)

/-- **Barycentric subdivision of singular chains.** The barycentric subdivision operator on the
singular chain complexes with coefficients in `R`, as a natural transformation of functors
`TopCat ⥤ ChainComplex C ℕ`. -/
def singularSubdivision :
    (singularChainComplexFunctor C).obj R ⟶ (singularChainComplexFunctor C).obj R where
  app X := singularSubdivisionChainMap R X
  naturality X Y f := by
    ext n : 1
    refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun σ ↦ ?_
    simp [singularChainComplexFunctor, Preadditive.sum_comp, Units.smul_def]

@[simp]
lemma singularSubdivision_app (X : TopCat.{w}) :
    (singularSubdivision R).app X = singularSubdivisionChainMap R X := (rfl)

end TauCeti
