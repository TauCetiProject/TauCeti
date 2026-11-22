/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import TauCeti.RepresentationTheory.Continuous.GeneralLinear
public import TauCeti.Topology.Algebra.IntermediateField

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Baire.Lemmas
import TauCeti.LinearAlgebra.LinearMap.BaseChange
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Subfield
import TauCeti.NumberTheory.Padics.AlgebraicClosure.IntermediateField
import TauCeti.RepresentationTheory.Continuous.StableLattice

/-!
# Coefficient-field and integral descent for continuous representations

Let `Γ` be a compact Baire topological group (for instance any compact Hausdorff group) and `ℓ` a
prime. Every continuous matrix representation `ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` has its image
contained in `GL ι E` for a single finite extension `E / ℚ_[ℓ]` inside `PadicAlgCl ℓ`, which may
be chosen to contain any prescribed finite intermediate field `K`.

The proof is a Baire-category argument: the finite subextensions `E` of `PadicAlgCl ℓ / ℚ_[ℓ]`
are countably many (`PadicAlgCl.countable_finiteDimensional`) and closed
(`Submodule.isClosed_of_finiteDimensional`), so the closed subgroups `H_E = ρ⁻¹(GL ι E)` form a
countable closed cover of the compact Baire group `Γ`. One `H_{E₀}` therefore has nonempty
interior, hence is open of finite index in `Γ`; adjoining the finitely many matrix entries of
coset representatives to `E₀ ⊔ K` yields a finite extension `E` containing `ρ(Γ)`.

Using the matrix–representation bridges in `TauCeti.RepresentationTheory.Continuous.GeneralLinear`
and stable lattices in `TauCeti.RepresentationTheory.Continuous.StableLattice`, we deduce:
* **Abstract Baire descent** (`TauCeti.ContinuousRep.baire_descent_of_countable`) for any compact
  Baire group and algebraic extension with countably many closed finite subextensions, specialized
  to `PadicAlgCl ℓ` in `TauCeti.ContinuousRep.baire_descent`.
* **Simultaneous descent of finite diagrams**
  (`TauCeti.ContinuousRep.exists_descent_family_of_countable`,
  `TauCeti.ContinuousRep.exists_descent_family`) and of a single representation
  (`TauCeti.ContinuousRep.exists_descent_of_countable`, `TauCeti.ContinuousRep.exists_descent`)
  for finite-dimensional continuous representations carrying the module topology
  (`IsModuleTopology`), with the descent isomorphism holding for any module topology on the
  base-changed spaces. Together with `TauCeti.RepresentationTheory.Descent`, this shows that the
  category of finite-dimensional continuous representations over `PadicAlgCl ℓ` carrying the
  module topology is the filtered 2-colimit of those over finite extensions of `ℚ_[ℓ]`.
* **Integral descent** (`TauCeti.ContinuousRep.exists_integral_conj_GL`): combining
  `baire_descent` with `TauCeti.ContinuousRep.exists_conj_mem_integerRing_GL` over the resulting
  finite extension `E / ℚ_[ℓ]` shows every continuous `ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` is
  conjugate into `GL ι 𝒪[E]`, i.e., to matrices with entries in `E` of norm at most `1`.

## Main results

* `TauCeti.ContinuousRep.baire_descent_of_countable`
* `TauCeti.ContinuousRep.baire_descent`
* `TauCeti.ContinuousRep.exists_descent_family_of_countable`
* `TauCeti.ContinuousRep.exists_descent_of_countable`
* `TauCeti.ContinuousRep.exists_descent_family`
* `TauCeti.ContinuousRep.exists_descent`
* `TauCeti.ContinuousRep.exists_integral_conj_GL`

## References

* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *$\hat{G}$-local systems on smooth projective
  curves are potentially automorphic*, Acta Math. 223 (2019), Theorem 4.8.
* F. Calegari and D. Geraghty, *Minimal modularity lifting for nonregular symplectic
  representations*, Duke Math. J. 169 (2020), §6.2, Proposition 6.8.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open Matrix IntermediateField ValuativeRel
open scoped TensorProduct Topology

namespace TauCeti.ContinuousRep

section BaireDescent

/-- The subgroup of elements whose image matrices have all entries in a subfield `E`. -/
private def entriesSubgroup {Γ L S ι : Type*} [Group Γ] [Field L] [SetLike S L]
    [SubfieldClass S L] [Fintype ι] [DecidableEq ι] (ρ : Γ →* GL ι L) (E : S) : Subgroup Γ :=
  (Matrix.GeneralLinearGroup.map (n := ι) (SubringClass.subtype E)).range.comap ρ

private theorem mem_entriesSubgroup_iff {Γ L S ι : Type*} [Group Γ] [Field L] [SetLike S L]
    [SubfieldClass S L] [Fintype ι] [DecidableEq ι] (ρ : Γ →* GL ι L) (E : S) (g : Γ) :
    g ∈ entriesSubgroup ρ E ↔ ∀ i j, (ρ g : Matrix ι ι L) i j ∈ E :=
  Matrix.GeneralLinearGroup.mem_range_map_subtype_iff E (ρ g)

private theorem isClosed_entriesSubgroup {Γ L S ι : Type*} [Group Γ] [TopologicalSpace Γ]
    [Field L] [SetLike S L] [SubfieldClass S L] [TopologicalSpace L] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι L) {E : S} (hE : IsClosed (E : Set L)) :
    IsClosed (entriesSubgroup (ρ : Γ →* GL ι L) E : Set Γ) := by
  have heq : (entriesSubgroup (ρ : Γ →* GL ι L) E : Set Γ) =
      ⋂ i, ⋂ j, (fun g : Γ ↦ (ρ g : Matrix ι ι L) i j) ⁻¹' (E : Set L) := by
    ext g
    simp [mem_entriesSubgroup_iff]
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦
    hE.preimage ((Units.continuous_val.comp (map_continuous ρ)).matrix_elem i j)

/-- **Abstract Baire-category descent for continuous matrix representations.** If `Γ` is a
compact Baire group and `L / K` is an algebraic field extension whose finite intermediate fields
are countably many and closed in `L`, then every continuous `ρ : Γ →ₜ* GL ι L` has entries in a
single finite intermediate field containing any prescribed finite `K₀`. -/
theorem baire_descent_of_countable
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [TopologicalSpace L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcount : {E : IntermediateField K L | FiniteDimensional K E}.Countable)
    (hclosed : ∀ E : IntermediateField K L, FiniteDimensional K E → IsClosed (E : Set L))
    (ρ : Γ →ₜ* GL ι L)
    (K₀ : IntermediateField K L) [FiniteDimensional K K₀] :
    ∃ E : IntermediateField K L, K₀ ≤ E ∧ FiniteDimensional K E ∧
      ∀ (g : Γ) (i j : ι), (ρ g : Matrix ι ι L) i j ∈ E := by
  let S := {E : IntermediateField K L | FiniteDimensional K E}
  have : Countable S := hcount.to_subtype
  let H (E : S) : Subgroup Γ := entriesSubgroup (ρ : Γ →* GL ι L) E.val
  have hHclosed (E : S) : IsClosed (H E : Set Γ) :=
    isClosed_entriesSubgroup ρ (hclosed E.val E.property)
  have hcover : (⋃ E : S, (H E : Set Γ)) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun g ↦ ?_
    let s : Set L := Set.range fun p : ι × ι ↦ (ρ g : Matrix ι ι L) p.1 p.2
    have : Finite s := Set.finite_range _
    refine Set.mem_iUnion.mpr ⟨⟨IntermediateField.adjoin K s,
      IntermediateField.finiteDimensional_adjoin fun x _ ↦
        (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩, ?_⟩
    exact (mem_entriesSubgroup_iff (ρ : Γ →* GL ι L) _ g).mpr fun i j ↦
      IntermediateField.subset_adjoin K s ⟨(i, j), rfl⟩
  -- By Baire category, some `H E₀` has nonempty interior, hence is open of finite index.
  obtain ⟨E₀, ⟨x, hx⟩⟩ := nonempty_interior_of_iUnion_of_closed hHclosed hcover
  have hopen : IsOpen (H E₀ : Set Γ) :=
    (H E₀).isOpen_of_mem_nhds (g := x) (mem_interior_iff_mem_nhds.mp hx)
  have : Finite (Γ ⧸ H E₀) := (H E₀).quotient_finite_of_isOpen hopen
  let T : Set L := Set.range fun p : (Γ ⧸ H E₀) × ι × ι ↦
    (ρ (Quotient.out p.1) : Matrix ι ι L) p.2.1 p.2.2
  have : Finite T := Set.finite_range _
  have : FiniteDimensional K E₀.val := E₀.property
  have : FiniteDimensional K (IntermediateField.adjoin K T) :=
    IntermediateField.finiteDimensional_adjoin fun y _ ↦
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let E : IntermediateField K L := K₀ ⊔ E₀.val ⊔ IntermediateField.adjoin K T
  refine ⟨E, le_sup_of_le_left le_sup_left, inferInstance, fun g i j ↦ ?_⟩
  let q : Γ ⧸ H E₀ := QuotientGroup.mk g
  let r : Γ := Quotient.out q
  have hrg : r⁻¹ * g ∈ H E₀ := by
    rw [← QuotientGroup.eq]
    exact Quotient.out_eq q
  have hrg' := (mem_entriesSubgroup_iff (ρ : Γ →* GL ι L) E₀.val (r⁻¹ * g)).mp hrg
  rw [← mul_inv_cancel_left r g, map_mul, Units.val_mul, Matrix.mul_apply]
  refine E.sum_mem fun k _ ↦ E.mul_mem ?_ ?_
  · exact (le_sup_right : IntermediateField.adjoin K T ≤ E)
      (IntermediateField.subset_adjoin K T ⟨(q, i, k), rfl⟩)
  · exact (le_sup_of_le_left le_sup_right : E₀.val ≤ E) (hrg' k j)

/-- **Coefficient-field descent from `PadicAlgCl ℓ`.** Every continuous matrix representation
`ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Baire group has entries in a single finite extension
`E / ℚ_[ℓ]` containing any prescribed finite intermediate field `K`. -/
theorem baire_descent {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ] (ℓ : ℕ) [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), K ≤ E ∧ FiniteDimensional ℚ_[ℓ] E ∧
      ∀ (g : Γ) (i j : ι), (ρ g : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E :=
  baire_descent_of_countable (PadicAlgCl.countable_finiteDimensional ℓ)
    (fun E _ ↦ E.toSubmodule.isClosed_of_finiteDimensional) ρ K

end BaireDescent

section DiagramDescent

/-- **Single-object descent isomorphism.** Given a continuous representation `ρ` over `L` whose
matrix entries in a basis `b` lie in `E : IntermediateField K L`, its lift `ofGL (liftGL (toGL ρ b)
E hmem)` base-changed back to `L` is continuously isomorphic to `ρ`. -/
private noncomputable def descentObjectIso {Γ K L V ι : Type*}
    [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
    [Field K] [Field L] [Algebra K L] [TopologicalSpace L] [IsTopologicalRing L]
    [AddCommGroup V] [Module L V] [TopologicalSpace V] [IsModuleTopology L V]
    [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ L V) (b : Module.Basis ι L V) (E : IntermediateField K L)
    (hmem : ∀ (g : Γ) (r c : ι), (toGL ρ b g : Matrix ι ι L) r c ∈ E)
    [TopologicalSpace (L ⊗[E] (ι → E))] [IsModuleTopology L (L ⊗[E] (ι → E))] :
    ((ofGL (liftGL (toGL ρ b) E hmem)).baseChange L).Iso ρ :=
  have hcomp :
      ContinuousMonoidHom.comp
        (continuousMapGL (algebraMap E L) (continuous_algebraMap E L))
        (liftGL (toGL ρ b) E hmem) = toGL ρ b := by
    ext1 g
    simp [map_liftGL_intermediateField]
  ((baseChangeOfGLIso L (liftGL (toGL ρ b) E hmem)).trans (ofGLCongr hcomp)).trans
    (ofGLToGLIso ρ b)

private theorem descentObjectIso_apply {Γ K L V ι : Type*}
    [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
    [Field K] [Field L] [Algebra K L] [TopologicalSpace L] [IsTopologicalRing L]
    [AddCommGroup V] [Module L V] [TopologicalSpace V] [IsModuleTopology L V]
    [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ L V) (b : Module.Basis ι L V) (E : IntermediateField K L)
    (hmem : ∀ (g : Γ) (r c : ι), (toGL ρ b g : Matrix ι ι L) r c ∈ E)
    [TopologicalSpace (L ⊗[E] (ι → E))] [IsModuleTopology L (L ⊗[E] (ι → E))]
    (x : L ⊗[E] (ι → E)) :
    descentObjectIso ρ b E hmem x = b.equivFun.symm (TensorProduct.piScalarRight E L L ι x) := by
  simp only [descentObjectIso, Iso.trans_apply, baseChangeOfGLIso_apply, ofGLCongr_apply,
    ofGLToGLIso_apply]

/-- **Topology-free intertwining descent.** If `M₁`, `M₂`, `M` lift the matrices of linear maps
`T₁ : V₁ →ₗ[L] V₁`, `T₂ : V₂ →ₗ[L] V₂`, `f : V₁ →ₗ[L] V₂` in bases `b₁`, `b₂` with
`f ∘ₗ T₁ = T₂ ∘ₗ f`, then `Matrix.mulVecLin M ∘ₗ Matrix.mulVecLin M₁ = Matrix.mulVecLin M₂ ∘ₗ
Matrix.mulVecLin M`. -/
private theorem mulVecLin_comp_eq_of_matrix_eq
    {E L V₁ V₂ ι₁ ι₂ : Type*} [Field E] [Field L] [Algebra E L]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (b₁ : Module.Basis ι₁ L V₁) (b₂ : Module.Basis ι₂ L V₂)
    (T₁ : V₁ →ₗ[L] V₁) (T₂ : V₂ →ₗ[L] V₂) (f : V₁ →ₗ[L] V₂) (hf : f ∘ₗ T₁ = T₂ ∘ₗ f)
    (M₁ : Matrix ι₁ ι₁ E) (M₂ : Matrix ι₂ ι₂ E) (M : Matrix ι₂ ι₁ E)
    (h₁ : M₁.map (algebraMap E L) = LinearMap.toMatrix b₁ b₁ T₁)
    (h₂ : M₂.map (algebraMap E L) = LinearMap.toMatrix b₂ b₂ T₂)
    (hM : M.map (algebraMap E L) = LinearMap.toMatrix b₁ b₂ f) :
    Matrix.mulVecLin M ∘ₗ Matrix.mulVecLin M₁ = Matrix.mulVecLin M₂ ∘ₗ Matrix.mulVecLin M := by
  apply LinearMap.baseChange_injective (R := E) (A := L)
  refine LinearMap.ext fun x ↦
    (b₂.equivFun.symm.injective.comp (TensorProduct.piScalarRight E L L ι₂).injective) ?_
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply, Function.comp_apply]
  rw [TensorProduct.piScalarRight_equivFun_intertwining b₁ b₂ f M hM,
    TensorProduct.piScalarRight_equivFun_intertwining b₁ b₁ T₁ M₁ h₁,
    TensorProduct.piScalarRight_equivFun_intertwining b₂ b₂ T₂ M₂ h₂,
    TensorProduct.piScalarRight_equivFun_intertwining b₁ b₂ f M hM]
  exact LinearMap.congr_fun hf _

/-- **Single-morphism descent.** Given a matrix `ME` over `E` lifting the matrix of an intertwining
map `f : ρ₁ → ρ₂` in bases `b₁`, `b₂`, `Matrix.mulVecLin ME` intertwines the descended matrix
representations `ofGL (liftGL (toGL ρ₁ b₁) E h₁)` and `ofGL (liftGL (toGL ρ₂ b₂) E h₂)`. -/
private noncomputable def descentIntertwiningMap {Γ K L V₁ V₂ ι₁ ι₂ : Type*}
    [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
    [Field K] [Field L] [Algebra K L] [TopologicalSpace L] [IsTopologicalRing L]
    [AddCommGroup V₁] [Module L V₁] [TopologicalSpace V₁] [IsModuleTopology L V₁]
    [AddCommGroup V₂] [Module L V₂] [TopologicalSpace V₂] [IsModuleTopology L V₂]
    [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (ρ₁ : ContinuousRep Γ L V₁) (ρ₂ : ContinuousRep Γ L V₂)
    (b₁ : Module.Basis ι₁ L V₁) (b₂ : Module.Basis ι₂ L V₂)
    (f : Representation.IntertwiningMap ρ₁.toRepresentation ρ₂.toRepresentation)
    (E : IntermediateField K L)
    (h₁ : ∀ (g : Γ) (r c : ι₁), (toGL ρ₁ b₁ g : Matrix ι₁ ι₁ L) r c ∈ E)
    (h₂ : ∀ (g : Γ) (r c : ι₂), (toGL ρ₂ b₂ g : Matrix ι₂ ι₂ L) r c ∈ E)
    (ME : Matrix ι₂ ι₁ E)
    (hME : ME.map (algebraMap E L) = LinearMap.toMatrix b₁ b₂ f.toLinearMap) :
    Representation.IntertwiningMap
      (ofGL (liftGL (toGL ρ₁ b₁) E h₁)).toRepresentation
      (ofGL (liftGL (toGL ρ₂ b₂) E h₂)).toRepresentation where
  toLinearMap := Matrix.mulVecLin ME
  isIntertwining' g := by
    have h := mulVecLin_comp_eq_of_matrix_eq b₁ b₂ (ρ₁ g) (ρ₂ g) f.toLinearMap
      (f.isIntertwining' g) (liftGL (toGL ρ₁ b₁) E h₁ g : Matrix ι₁ ι₁ E)
      (liftGL (toGL ρ₂ b₂) E h₂ g : Matrix ι₂ ι₂ E) ME
      (by
        ext i j
        simp only [Matrix.map_apply, IntermediateField.algebraMap_apply, coe_liftGL,
          coe_toGL_apply, LinearMap.toMatrix_apply])
      (by
        ext i j
        simp only [Matrix.map_apply, IntermediateField.algebraMap_apply, coe_liftGL,
          coe_toGL_apply, LinearMap.toMatrix_apply])
      hME
    refine LinearMap.ext fun v ↦ ?_
    simpa only [LinearMap.comp_apply, Matrix.mulVecLin_apply, coe_toRepresentation,
      ofGL_apply] using LinearMap.congr_fun h v

/-- **Abstract simultaneous descent of a finite diagram of continuous representations.** Let `Γ`
be a compact Baire group with continuous inversion and `L / K` an algebraic extension of
topological fields whose finite intermediate fields are countably many and closed in `L`. Any
finite family of finite-dimensional continuous representations of `Γ` over `L` carrying the
`L`-module topology (`IsModuleTopology L (V a)`), together with finitely many intertwining maps
between them, descends to a single finite intermediate field `E` containing any prescribed finite
`K₀`. The descent isomorphisms hold for any `L`-module topology (`IsModuleTopology L`) on the
base-changed spaces `L ⊗[E] (Fin _ → E)`. -/
theorem exists_descent_family_of_countable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [ContinuousInv Γ] [CompactSpace Γ] [BaireSpace Γ]
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [TopologicalSpace L] [IsTopologicalRing L]
    (hcount : {E : IntermediateField K L | FiniteDimensional K E}.Countable)
    (hclosed : ∀ E : IntermediateField K L, FiniteDimensional K E → IsClosed (E : Set L))
    {α β : Type*} [Finite α] [Finite β]
    {V : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module L (V a)]
    [∀ a, FiniteDimensional L (V a)]
    [∀ a, TopologicalSpace (V a)] [∀ a, IsModuleTopology L (V a)]
    (ρ : ∀ a : α, ContinuousRep Γ L (V a))
    {src dst : β → α}
    (f : ∀ j : β, Representation.IntertwiningMap
      (ρ (src j)).toRepresentation (ρ (dst j)).toRepresentation)
    (K₀ : IntermediateField K L) [FiniteDimensional K K₀] :
    ∃ (E : IntermediateField K L) (_ : FiniteDimensional K E)
      (ρE : ∀ a : α, ContinuousRep Γ E (Fin (Module.finrank L (V a)) → E))
      (fE : ∀ j : β, Representation.IntertwiningMap
        (ρE (src j)).toRepresentation (ρE (dst j)).toRepresentation),
      K₀ ≤ E ∧
        ∀ [∀ a, TopologicalSpace (L ⊗[E] (Fin (Module.finrank L (V a)) → E))]
          [∀ a, IsModuleTopology L (L ⊗[E] (Fin (Module.finrank L (V a)) → E))],
          ∃ e : ∀ a : α, ((ρE a).baseChange L).Iso (ρ a),
            ∀ (j : β) (x),
              e (dst j) ((fE j).baseChange L x) = f j (e (src j) x) := by
  -- 1. Descend each object representation via Baire category and adjoin morphism matrix entries.
  let b (a : α) := Module.finBasis L (V a)
  choose Eobj _ hfinObj hmemObj using fun a ↦
    baire_descent_of_countable hcount hclosed (toGL (ρ a) (b a)) K₀
  let M (j : β) := LinearMap.toMatrix (b (src j)) (b (dst j)) (f j).toLinearMap
  let Emor (j : β) : IntermediateField K L :=
    IntermediateField.adjoin K (Set.range fun p : _ × _ ↦ M j p.1 p.2)
  have hfinMor (j : β) : FiniteDimensional K (Emor j) := by
    have : Finite (Set.range fun p : _ × _ ↦ M j p.1 p.2) := Set.finite_range _
    exact IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  -- 2. Take the finite compositum `E` containing `K₀`, all `Eobj a`, and all `Emor j`.
  let E : IntermediateField K L := K₀ ⊔ (⨆ a, Eobj a) ⊔ (⨆ j, Emor j)
  have hmemE (a : α) (g : Γ) (r c : Fin (Module.finrank L (V a))) :
      (toGL (ρ a) (b a) g : Matrix _ _ L) r c ∈ E :=
    le_sup_of_le_left (le_sup_of_le_right (le_iSup Eobj a)) (hmemObj a g r c)
  let ρE (a : α) : ContinuousRep Γ E (Fin (Module.finrank L (V a)) → E) :=
    ofGL (liftGL (toGL (ρ a) (b a)) E (hmemE a))
  -- 3. Lift each intertwining matrix to `E` and verify equivariance topology-freely.
  have hmorE (j : β) : Emor j ≤ E := le_trans (le_iSup Emor j) le_sup_right
  let ME (j : β) : Matrix _ _ E := Matrix.of fun r c ↦
    ⟨M j r c, hmorE j (IntermediateField.subset_adjoin K _ ⟨(r, c), rfl⟩)⟩
  have hME (j : β) : (ME j).map (algebraMap E L) = M j := by
    ext r c
    simp only [Matrix.map_apply, ME, Matrix.of_apply, IntermediateField.algebraMap_apply]
  let fE (j : β) := descentIntertwiningMap (ρ (src j)) (ρ (dst j)) (b (src j)) (b (dst j))
    (f j) E (hmemE (src j)) (hmemE (dst j)) (ME j) (hME j)
  -- 4. Package the descent isomorphisms for any `L`-module topology on the base-changed spaces.
  refine ⟨E, inferInstance, ρE, fE, le_sup_of_le_left le_sup_left, ?_⟩
  intro _ _
  refine ⟨fun a ↦ descentObjectIso (ρ a) (b a) E (hmemE a), fun j x ↦ ?_⟩
  rw [descentObjectIso_apply, descentObjectIso_apply]
  simpa only [fE, descentIntertwiningMap, ← Representation.IntertwiningMap.coe_toLinearMap,
    Representation.IntertwiningMap.toLinearMap_baseChange] using
    TensorProduct.piScalarRight_equivFun_intertwining (b (src j)) (b (dst j))
      (f j).toLinearMap (ME j) (hME j) x

/-- **Abstract object descent for a continuous representation.** Under the hypotheses of
`exists_descent_family_of_countable`, every finite-dimensional continuous representation `ρ` of a
compact Baire group over `L` carrying the `L`-module topology (`IsModuleTopology L V`) descends to
a finite intermediate field `E` containing any prescribed finite `K₀`, with the descent
isomorphism holding for any `L`-module topology on `L ⊗[E] (Fin _ → E)`. -/
theorem exists_descent_of_countable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [ContinuousInv Γ] [CompactSpace Γ] [BaireSpace Γ]
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [TopologicalSpace L] [IsTopologicalRing L]
    (hcount : {E : IntermediateField K L | FiniteDimensional K E}.Countable)
    (hclosed : ∀ E : IntermediateField K L, FiniteDimensional K E → IsClosed (E : Set L))
    {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [TopologicalSpace V] [IsModuleTopology L V]
    (ρ : ContinuousRep Γ L V)
    (K₀ : IntermediateField K L) [FiniteDimensional K K₀] :
    ∃ (E : IntermediateField K L) (_ : FiniteDimensional K E)
      (ρE : ContinuousRep Γ E (Fin (Module.finrank L V) → E)),
      K₀ ≤ E ∧
        ∀ [TopologicalSpace (L ⊗[E] (Fin (Module.finrank L V) → E))]
          [IsModuleTopology L (L ⊗[E] (Fin (Module.finrank L V) → E))],
          Nonempty ((ρE.baseChange L).Iso ρ) := by
  obtain ⟨E, hfinE, ρE, _, hKE, he⟩ := exists_descent_family_of_countable hcount hclosed
    (α := Unit) (β := Empty) (V := fun _ ↦ V) (fun _ ↦ ρ) (src := Empty.elim) (dst := Empty.elim)
    (fun j ↦ j.elim) K₀
  refine ⟨E, hfinE, ρE (), hKE, ?_⟩
  intro hT hM
  obtain ⟨e, _⟩ := @he (fun _ ↦ hT) (fun _ ↦ hM)
  exact ⟨e ()⟩

/-- **Simultaneous descent of a finite diagram of continuous representations over `PadicAlgCl ℓ`.**
Any finite family of finite-dimensional continuous representations of a compact Baire group `Γ`
over `PadicAlgCl ℓ` carrying the module topology (`IsModuleTopology (PadicAlgCl ℓ) (V a)`),
together with finitely many intertwining maps between them, descends to a single finite extension
`E / ℚ_[ℓ]` containing any prescribed finite intermediate field `K`, with the descent isomorphisms
holding for any module topology on the base-changed spaces. -/
theorem exists_descent_family {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [ContinuousInv Γ] [CompactSpace Γ] [BaireSpace Γ]
    (ℓ : ℕ) [Fact ℓ.Prime] {α β : Type*} [Finite α] [Finite β]
    {V : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module (PadicAlgCl ℓ) (V a)]
    [∀ a, FiniteDimensional (PadicAlgCl ℓ) (V a)]
    [∀ a, TopologicalSpace (V a)] [∀ a, IsModuleTopology (PadicAlgCl ℓ) (V a)]
    (ρ : ∀ a : α, ContinuousRep Γ (PadicAlgCl ℓ) (V a))
    {src dst : β → α}
    (f : ∀ j : β, Representation.IntertwiningMap
      (ρ (src j)).toRepresentation (ρ (dst j)).toRepresentation)
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ∀ a : α, ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))
      (fE : ∀ j : β, Representation.IntertwiningMap
        (ρE (src j)).toRepresentation (ρE (dst j)).toRepresentation),
      K ≤ E ∧
        ∀ [∀ a, TopologicalSpace ((PadicAlgCl ℓ) ⊗[E]
            (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))]
          [∀ a, IsModuleTopology (PadicAlgCl ℓ) ((PadicAlgCl ℓ) ⊗[E]
            (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))],
          ∃ e : ∀ a : α, ((ρE a).baseChange (PadicAlgCl ℓ)).Iso (ρ a),
            ∀ (j : β) (x),
              e (dst j) ((fE j).baseChange (PadicAlgCl ℓ) x) = f j (e (src j) x) :=
  exists_descent_family_of_countable (PadicAlgCl.countable_finiteDimensional ℓ)
    (fun E _ ↦ E.toSubmodule.isClosed_of_finiteDimensional) ρ f K

/-- **Object descent for a continuous representation over `PadicAlgCl ℓ`.** Every
finite-dimensional continuous representation of a compact Baire group over `PadicAlgCl ℓ` carrying
the module topology (`IsModuleTopology (PadicAlgCl ℓ) V`) descends to a finite extension
`E / ℚ_[ℓ]` containing any prescribed finite `K`, with the descent isomorphism holding for any
module topology on the base-changed space. -/
theorem exists_descent {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [ContinuousInv Γ] [CompactSpace Γ] [BaireSpace Γ]
    (ℓ : ℕ) [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    [FiniteDimensional (PadicAlgCl ℓ) V] [TopologicalSpace V] [IsModuleTopology (PadicAlgCl ℓ) V]
    (ρ : ContinuousRep Γ (PadicAlgCl ℓ) V)
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) V) → E)),
      K ≤ E ∧
        ∀ [TopologicalSpace ((PadicAlgCl ℓ) ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))]
          [IsModuleTopology (PadicAlgCl ℓ)
            ((PadicAlgCl ℓ) ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))],
          Nonempty (((ρE.baseChange (PadicAlgCl ℓ)).Iso ρ)) :=
  exists_descent_of_countable (PadicAlgCl.countable_finiteDimensional ℓ)
    (fun E _ ↦ E.toSubmodule.isClosed_of_finiteDimensional) ρ K

end DiagramDescent

section IntegralDescent

/-- **Integral descent over `PadicAlgCl ℓ`.** Every continuous matrix representation
`ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Baire group is conjugate into `GL ι 𝒪[E]` for a
finite extension `E / ℚ_[ℓ]`: its conjugates have all entries in `E` of norm at most `1`. -/
theorem exists_integral_conj_GL {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [CompactSpace Γ] [BaireSpace Γ] (ℓ : ℕ) [Fact ℓ.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)) :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (P : GL ι (PadicAlgCl ℓ)),
      FiniteDimensional ℚ_[ℓ] E ∧ ∀ (g : Γ) (i j : ι),
        (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E ∧
        ‖(P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j‖ ≤ 1 := by
  obtain ⟨E, -, hfin, hE⟩ := baire_descent ℓ ρ ⊥
  let ρE : Γ →ₜ* GL ι E := liftGL ρ E hE
  -- Equip `E` with its spectral-norm local-field structure, whose topology is the subspace one.
  let : ValuativeRel E := TauCeti.algebraicExtensionValuativeRel ℚ_[ℓ] E
  have : IsNonarchimedeanLocalField E :=
    PadicAlgCl.finiteIntermediateField_isNonarchimedeanLocalField ℓ E
  obtain ⟨PE, hPE⟩ := exists_conj_mem_integerRing_GL ρE
  let P : GL ι (PadicAlgCl ℓ) := Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl ℓ)) PE
  refine ⟨E, P, hfin, fun g i j ↦ ?_⟩
  have hconj : P * ρ g * P⁻¹ =
      Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl ℓ)) (PE * ρE g * PE⁻¹) := by
    simp only [P, map_mul, map_inv, map_liftGL_intermediateField, ρE]
  have hval : (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j =
      (((PE * ρE g * PE⁻¹ : GL ι E) : Matrix ι ι E) i j : PadicAlgCl ℓ) := by
    rw [← Units.val_mul, ← Units.val_mul, hconj]
    simp only [Matrix.GeneralLinearGroup.map_apply, IntermediateField.algebraMap_apply]
  rw [hval]
  exact ⟨SetLike.coe_mem _,
    (PadicAlgCl.mem_integerRing_algebraicExtension_iff ℓ E _).mp
      (by simpa only [Units.val_mul] using hPE g i j)⟩

end IntegralDescent

end TauCeti.ContinuousRep
