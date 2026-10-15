/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.PiTensorProduct.Differential
public import TauCeti.Algebra.Homology.GradedCochainComplex

/-!
# Total-degree tensor complexes in characteristic two

The degree-`n` tensor piece is spanned by pure tensors of homogeneous factors whose degrees sum
to `n`. The finite tensor differential raises total degree by one. Over a ground ring of
characteristic two it therefore defines a cochain complex whenever the factor differentials
square to zero. A tensor of degree-`q` elements lies in degree `#ι * q`; tensors of cycles are
cycles. This is the degree multiplication in the tensor construction of the Evens norm.

The construction accepts families of submodules, without requiring a direct-sum decomposition:
its terms are precisely their total-degree tensor spans. In applications to graded modules,
these are the usual total-degree pieces. Degree-preserving factorwise maps commuting with
differentials induce cochain maps, preserving identities and composition.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open scoped TensorProduct

namespace TauCeti.PiTensorProduct

universe u v w

variable {R : Type u} {ι : Type v} [Fintype ι] {M : ι → Type w}

section Semiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The total-degree tensor piece: the span of pure tensors with homogeneous factor degrees
summing to `n`. -/
noncomputable def degreePiece (ℳ : ∀ i, ℤ → Submodule R (M i)) (n : ℤ) :
    Submodule R (⨂[R] i, M i) :=
  Submodule.span R {z | ∃ (q : ι → ℤ) (x : ∀ i, M i),
    (∑ i, q i) = n ∧ (∀ i, x i ∈ ℳ i (q i)) ∧ _root_.PiTensorProduct.tprod R x = z}

/-- The defining span of a total-degree tensor piece. -/
theorem degreePiece_def (ℳ : ∀ i, ℤ → Submodule R (M i)) (n : ℤ) :
    degreePiece ℳ n = Submodule.span R {z | ∃ (q : ι → ℤ) (x : ∀ i, M i),
      (∑ i, q i) = n ∧ (∀ i, x i ∈ ℳ i (q i)) ∧ _root_.PiTensorProduct.tprod R x = z} :=
  (rfl)

/-- A pure tensor of homogeneous factors belongs to the piece of their total degree. -/
theorem tprod_mem_degreePiece (ℳ : ∀ i, ℤ → Submodule R (M i)) (q : ι → ℤ)
    (x : ∀ i, M i) (hx : ∀ i, x i ∈ ℳ i (q i)) :
    _root_.PiTensorProduct.tprod R x ∈ degreePiece ℳ (∑ i, q i) :=
  Submodule.subset_span ⟨q, x, rfl, hx, rfl⟩

/-- A linear map sends the degree-`n` tensor piece into a submodule exactly when it sends
each homogeneous pure tensor of total degree `n` into that submodule. -/
theorem degreePiece_le_comap_iff {N : Type*} [AddCommMonoid N] [Module R N]
    (ℳ : ∀ i, ℤ → Submodule R (M i)) (n : ℤ) (f : (⨂[R] i, M i) →ₗ[R] N)
    (P : Submodule R N) :
    degreePiece ℳ n ≤ P.comap f ↔
      ∀ (q : ι → ℤ) (x : ∀ i, M i), (∑ i, q i) = n →
        (∀ i, x i ∈ ℳ i (q i)) → f (_root_.PiTensorProduct.tprod R x) ∈ P := by
  rw [degreePiece_def, Submodule.span_le]
  constructor
  · intro h q x hq hx
    exact h ⟨q, x, hq, hx, rfl⟩
  · rintro h z ⟨q, x, hq, hx, rfl⟩
    exact h q x hq hx

/-- Applying degree-zero maps factorwise preserves total degree. -/
theorem map_mem_degreePiece {N : ι → Type*} [∀ i, AddCommMonoid (N i)]
    [∀ i, Module R (N i)] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (𝒩 : ∀ i, ℤ → Submodule R (N i)) (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i, LinearMap.IsHomogeneous (f i) (ℳ i) (𝒩 i) 0) {n : ℤ}
    {z : ⨂[R] i, M i} (hz : z ∈ degreePiece ℳ n) :
    _root_.PiTensorProduct.map f z ∈ degreePiece 𝒩 n := by
  refine (degreePiece_le_comap_iff ℳ n (_root_.PiTensorProduct.map f) (degreePiece 𝒩 n)).2
    (fun q x hq hx ↦ ?_) hz
  rw [_root_.PiTensorProduct.map_tprod, ← hq]
  exact tprod_mem_degreePiece 𝒩 q _ fun i ↦ by
    simpa only [add_zero] using (hf i).map_mem (hx i)

/-- Reindexing a graded family preserves total degree. -/
theorem reindex_mem_degreePiece {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (ℳ : ∀ i, ℤ → Submodule R (M i)) {n : ℤ}
    {z : ⨂[R] i, M i} (hz : z ∈ degreePiece ℳ n) :
    _root_.PiTensorProduct.reindex R M e z ∈
      degreePiece (fun j ↦ ℳ (e.symm j)) n := by
  refine (degreePiece_le_comap_iff ℳ n
    (_root_.PiTensorProduct.reindex R M e).toLinearMap
    (degreePiece (fun j ↦ ℳ (e.symm j)) n)).2 (fun q x hq hx ↦ ?_) hz
  rw [LinearEquiv.coe_coe, _root_.PiTensorProduct.reindex_tprod,
    ← hq, ← Equiv.sum_comp e.symm]
  exact tprod_mem_degreePiece (fun j ↦ ℳ (e.symm j)) (fun j ↦ q (e.symm j)) _ fun j ↦ hx _

/-- Equal factor degrees multiply by the number of tensor factors. -/
theorem tprod_mem_degreePiece_const (ℳ : ∀ i, ℤ → Submodule R (M i)) (q : ℤ)
    (x : ∀ i, M i) (hx : ∀ i, x i ∈ ℳ i q) :
    _root_.PiTensorProduct.tprod R x ∈ degreePiece ℳ ((Fintype.card ι : ℤ) * q) := by
  simpa using tprod_mem_degreePiece ℳ (fun _ ↦ q) x hx

/-- The tensor differential raises total degree by one if every factor differential does. -/
theorem isHomogeneous_differential (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1) :
    LinearMap.IsHomogeneous (differential d) (degreePiece ℳ) (degreePiece ℳ) 1 := by
  classical
  rw [LinearMap.isHomogeneous_def]
  intro n z hz
  refine (degreePiece_le_comap_iff ℳ n (differential d) (degreePiece ℳ (n + 1))).2
    (fun q x hq hx ↦ ?_) hz
  rw [differential_tprod]
  apply Submodule.sum_mem
  intro i _
  have hsum : (∑ j, Function.update q i (q i + 1) j) = n + 1 := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hq
    omega
  rw [← hsum]
  apply tprod_mem_degreePiece
  intro j
  by_cases h : j = i
  · subst h
    simp only [Function.update_self]
    exact (hdeg j).map_mem (hx j)
  · simpa only [Function.update_of_ne h] using hx j

/-- A tensor of cycles is a cycle for the finite tensor differential. -/
theorem differential_tprod_eq_zero (d : ∀ i, Module.End R (M i))
    (x : ∀ i, M i) (hx : ∀ i, d i (x i) = 0) :
    differential d (_root_.PiTensorProduct.tprod R x) = 0 := by
  classical
  rw [differential_tprod]
  apply Finset.sum_eq_zero
  intro i _
  rw [hx i]
  exact (_root_.PiTensorProduct.tprod R).map_update_zero x i

end Semiring

section Ring

open CategoryTheory

variable [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- The total-degree tensor cochain complex in characteristic two. Its terms are the tensor
pieces and its differential is the restriction of the sum of the factor differentials. -/
noncomputable def cochainComplex [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) : CochainComplex (ModuleCat R) ℤ :=
  gradedCochainComplex (degreePiece ℳ) (differential d) (isHomogeneous_differential ℳ d hdeg)
    (fun _ x ↦ LinearMap.congr_fun (differential_comp_self d hd) x)

/-- The degree-`n` term is the total-degree tensor piece. -/
@[simp]
theorem cochainComplex_X [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).X n = ModuleCat.of R (degreePiece ℳ n) := by
  rw [cochainComplex, gradedCochainComplex_X]

/-- The complex differential is the restricted tensor differential, transported along the
identifications of its source and target degree pieces. -/
@[simp]
theorem cochainComplex_d [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).d n (n + 1) =
      eqToHom (cochainComplex_X ℳ d hdeg hd n) ≫
        ModuleCat.ofHom ((differential d).restrict
          (p := degreePiece ℳ n) (q := degreePiece ℳ (n + 1))
          fun _ hz ↦ (isHomogeneous_differential ℳ d hdeg).map_mem hz) ≫
        eqToHom (cochainComplex_X ℳ d hdeg hd (n + 1)).symm :=
  gradedCochainComplex_d n

/-- Under the degree-piece identification, the complex differential applies the finite tensor
differential to the underlying tensor. -/
theorem cochainComplex_d_apply [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) (z : degreePiece ℳ n) :
    CategoryTheory.eqToHom (cochainComplex_X ℳ d hdeg hd (n + 1))
        ((cochainComplex ℳ d hdeg hd).d n (n + 1)
          (CategoryTheory.eqToHom (cochainComplex_X ℳ d hdeg hd n).symm z)) =
      (⟨differential d z, (isHomogeneous_differential ℳ d hdeg).map_mem z.2⟩ :
        degreePiece ℳ (n + 1)) :=
  gradedCochainComplex_d_apply n z

/-- The degree-`n` term of the tensor cochain complex identified with its total-degree piece
as a linear equivalence. -/
noncomputable def cochainComplexXEquiv [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) :
    (cochainComplex ℳ d hdeg hd).X n ≃ₗ[R] degreePiece ℳ n :=
  gradedCochainComplexXEquiv (hdeg := isHomogeneous_differential ℳ d hdeg)
    (hsq := fun _ x ↦ LinearMap.congr_fun (differential_comp_self d hd) x) n

/-- Under the degree-piece equivalence, the complex differential applies the finite tensor
differential to the underlying tensor. -/
theorem cochainComplexXEquiv_d [CharP R 2] (ℳ : ∀ i, ℤ → Submodule R (M i))
    (d : ∀ i, Module.End R (M i))
    (hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1)
    (hd : ∀ i, d i ∘ₗ d i = 0) (n : ℤ) (z : (cochainComplex ℳ d hdeg hd).X n) :
    (cochainComplexXEquiv ℳ d hdeg hd (n + 1)
        (((cochainComplex ℳ d hdeg hd).d n (n + 1)).hom z) : ⨂[R] i, M i) =
      differential d (cochainComplexXEquiv ℳ d hdeg hd n z) := by
  dsimp only [cochainComplexXEquiv]
  exact gradedCochainComplexXEquiv_d n z

section Map

variable [CharP R 2] {N P : ι → Type w}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)]
  {ℳ : ∀ i, ℤ → Submodule R (M i)} {𝒩 : ∀ i, ℤ → Submodule R (N i)}
  {𝒦 : ∀ i, ℤ → Submodule R (P i)}
  {d : ∀ i, Module.End R (M i)} {e : ∀ i, Module.End R (N i)}
  {k : ∀ i, Module.End R (P i)}
  {hdeg : ∀ i, LinearMap.IsHomogeneous (d i) (ℳ i) (ℳ i) 1}
  {hedeg : ∀ i, LinearMap.IsHomogeneous (e i) (𝒩 i) (𝒩 i) 1}
  {hkdeg : ∀ i, LinearMap.IsHomogeneous (k i) (𝒦 i) (𝒦 i) 1}
  {hd : ∀ i, d i ∘ₗ d i = 0} {he : ∀ i, e i ∘ₗ e i = 0}
  {hk : ∀ i, k i ∘ₗ k i = 0}

/-- Degree-preserving factorwise maps commuting with differentials induce a map of total-degree
tensor cochain complexes. -/
noncomputable def cochainComplexMap (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i, LinearMap.IsHomogeneous (f i) (ℳ i) (𝒩 i) 0)
    (hcomm : ∀ i, e i ∘ₗ f i = f i ∘ₗ d i) :
    cochainComplex ℳ d hdeg hd ⟶ cochainComplex 𝒩 e hedeg he :=
  CochainComplex.ofHom (fun n ↦
    eqToHom (cochainComplex_X ℳ d hdeg hd n) ≫
      ModuleCat.ofHom ((_root_.PiTensorProduct.map f).restrict
        (fun _ hz ↦ map_mem_degreePiece ℳ 𝒩 f hf hz)) ≫
      eqToHom (cochainComplex_X 𝒩 e hedeg he n).symm) (fun n ↦ by
    rw [cochainComplex_d, cochainComplex_d]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    apply (cancel_epi _).2
    simp only [← Category.assoc]
    apply (cancel_mono _).2
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact LinearMap.congr_fun (differential_comp_map d e f hcomm) z)

/-- Each component is the tensor of the factor maps restricted to the total-degree piece. -/
@[simp]
theorem cochainComplexMap_f (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i, LinearMap.IsHomogeneous (f i) (ℳ i) (𝒩 i) 0)
    (hcomm : ∀ i, e i ∘ₗ f i = f i ∘ₗ d i) (n : ℤ) :
    (cochainComplexMap (hdeg := hdeg) (hd := hd) (hedeg := hedeg) (he := he)
      f hf hcomm).f n =
      eqToHom (cochainComplex_X ℳ d hdeg hd n) ≫
        ModuleCat.ofHom ((_root_.PiTensorProduct.map f).restrict
          (fun _ hz ↦ map_mem_degreePiece ℳ 𝒩 f hf hz)) ≫
        eqToHom (cochainComplex_X 𝒩 e hedeg he n).symm :=
  (rfl)

/-- Under the degree-piece identifications, the induced map applies the factor maps. -/
theorem cochainComplexMap_f_apply (f : ∀ i, M i →ₗ[R] N i)
    (hf : ∀ i, LinearMap.IsHomogeneous (f i) (ℳ i) (𝒩 i) 0)
    (hcomm : ∀ i, e i ∘ₗ f i = f i ∘ₗ d i) (n : ℤ) (z : degreePiece ℳ n) :
    eqToHom (cochainComplex_X 𝒩 e hedeg he n)
      ((cochainComplexMap (hdeg := hdeg) (hd := hd) (hedeg := hedeg) (he := he)
        f hf hcomm).f n (eqToHom (cochainComplex_X ℳ d hdeg hd n).symm z)) =
      (⟨_root_.PiTensorProduct.map f z, map_mem_degreePiece ℳ 𝒩 f hf z.2⟩ :
        degreePiece 𝒩 n) := by
  -- Compose before evaluating so the degree-piece transports cancel categorically.
  have h := congrArg (fun t ↦ t z)
    (show eqToHom (cochainComplex_X ℳ d hdeg hd n).symm ≫
        (cochainComplexMap (hdeg := hdeg) (hd := hd) (hedeg := hedeg) (he := he)
          f hf hcomm).f n ≫ eqToHom (cochainComplex_X 𝒩 e hedeg he n) =
        ModuleCat.ofHom ((_root_.PiTensorProduct.map f).restrict
          (fun _ hz ↦ map_mem_degreePiece ℳ 𝒩 f hf hz)) by
      rw [cochainComplexMap_f]
      simp)
  exact h

/-- Tensoring the identity factor maps induces the identity cochain map. -/
@[simp]
theorem cochainComplexMap_id :
    cochainComplexMap (d := d) (e := d) (hdeg := hdeg) (hd := hd) (hedeg := hdeg) (he := hd)
      (fun _ ↦ LinearMap.id) (fun i ↦ LinearMap.isHomogeneous_id (ℳ i))
      (fun _ ↦ by simp) = 𝟙 (cochainComplex ℳ d hdeg hd) := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [cochainComplexMap_f, _root_.PiTensorProduct.map_id, HomologicalComplex.id_f]
  have h : ModuleCat.ofHom ((LinearMap.id : Module.End R (⨂[R] i, M i)).restrict
      (p := degreePiece ℳ n) (q := degreePiece ℳ n) (fun _ hz ↦ hz)) = 𝟙 _ := rfl
  rw [h]
  simp

/-- Tensor cochain maps preserve composition of factorwise chain maps. This is an explicit
rewrite lemma since the intermediate differential cannot be inferred from the composite. -/
theorem cochainComplexMap_comp (f : ∀ i, M i →ₗ[R] N i) (g : ∀ i, N i →ₗ[R] P i)
    (hf : ∀ i, LinearMap.IsHomogeneous (f i) (ℳ i) (𝒩 i) 0)
    (hg : ∀ i, LinearMap.IsHomogeneous (g i) (𝒩 i) (𝒦 i) 0)
    (hcommf : ∀ i, e i ∘ₗ f i = f i ∘ₗ d i)
    (hcommg : ∀ i, k i ∘ₗ g i = g i ∘ₗ e i) :
    cochainComplexMap (hdeg := hdeg) (hd := hd) (hedeg := hkdeg) (he := hk)
      (fun i ↦ g i ∘ₗ f i) (fun i ↦ by simpa using (hg i).comp (hf i))
      (fun i ↦ by rw [← LinearMap.comp_assoc, hcommg i, LinearMap.comp_assoc,
        hcommf i, LinearMap.comp_assoc]) =
      cochainComplexMap (hdeg := hdeg) (hd := hd) (hedeg := hedeg) (he := he)
        f hf hcommf ≫
      cochainComplexMap (hdeg := hedeg) (hd := he) (hedeg := hkdeg) (he := hk)
        g hg hcommg := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, cochainComplexMap_f, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  apply (cancel_epi _).2
  simp only [← Category.assoc]
  apply (cancel_mono _).2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (_root_.PiTensorProduct.map_comp g f) z.val

end Map

end Ring

end TauCeti.PiTensorProduct
