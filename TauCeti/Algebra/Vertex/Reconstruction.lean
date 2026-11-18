/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.NthProduct
import TauCeti.Algebra.Vertex.FormalDistribution
import TauCeti.Algebra.Module.Rat

/-!
# State–field correspondence and the vertex algebra reconstruction theorem

In a formal vertex algebra over a `ℚ`-algebra `R`, the state–field map intertwines every mode
product `a₍ₙ₎ b` (`n : ℤ`) with the `n`-th field product `Y(a, z)₍ₙ₎ Y(b, z)`
(`TauCeti.FormalVertexAxioms.field_ncoeff_apply`). Specializing `n` expresses the field of a
nonnegative mode `a₍ₙ₎ b` (`n : ℕ`) as `Res_z (z - w)ⁿ [Y(a, z), Y(b, w)]` and the field of a
negative mode `a₍₋ₖ₋₁₎ b` as the divided-power normal-ordered product
`(k!)⁻¹ : (∂_z^k Y(a, z)) Y(b, z) :` (in particular, `Y(a₍₋₁₎ b, z) = :Y(a, z) Y(b, z):`).

Conversely, given an `R`-module `V` over a `ℚ`-algebra `R`, a vacuum vector `vac`, an endomorphism
`T` killing `vac`, and a family of pairwise local fields `F : ι → VertexOperator R V` covariant
with `T` whose modes generate `V` from `vac`, there is a unique formal vertex algebra structure on
`V` with vacuum `vac`, translation `T`, and `Y(((F i)[[-1]]) vac, z) = F i`
(`TauCeti.FormalVertexAxioms.ofGeneratingFields`,
`TauCeti.FormalVertexAxioms.existsUnique_of_generatingFields`). Notably, lower truncation of each
field `F i` combined with `[T, (F i)[[n]]] = (∂(F i))[[n]]` and `T vac = 0` automatically implies
that `F i` annihilates `vac` in all nonnegative modes, and no `vac ≠ 0` hypothesis is needed.

## Main definitions

* `TauCeti.FormalVertexAxioms.ofGeneratingFields`: the formal vertex algebra reconstructed from a
  family of pairwise local, translation-covariant generating fields.

## Main results

* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: state–field correspondence
  `Y(a₍ₙ₎ b, z) = Y(a, z)₍ₙ₎ Y(b, z)` for all `n : ℤ`.
* `TauCeti.FormalVertexAxioms.field_ncoeff_natCast_apply`,
  `TauCeti.FormalVertexAxioms.field_ncoeff_neg_one_apply`,
  `TauCeti.FormalVertexAxioms.field_ncoeff_neg_apply`: specializations to residue products, normal
  ordering, and negative modes.
* `TauCeti.FormalVertexAxioms.ofGeneratingFields_field_ncoeff_neg_one_apply`,
  `TauCeti.FormalVertexAxioms.ofGeneratingFields_field_ncoeff_apply`: evaluation of the
  reconstructed state–field map on generating states and PBW words.
* `TauCeti.FormalVertexAxioms.eq_of_field_eq`,
  `TauCeti.FormalVertexAxioms.eq_ofGeneratingFields`,
  `TauCeti.FormalVertexAxioms.existsUnique_of_generatingFields`: extensionality on generating
  states, uniqueness, and existence-uniqueness of the reconstructed formal vertex algebra.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.4–§4.5 (Theorem 4.5, the existence theorem).
* V. Kac, *Introduction to vertex algebras, Poisson vertex algebras, and integrable Hamiltonian
  systems*, Theorem 1.1.
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Theorem 3.2.10.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.3, Theorem 2.3.11.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator

namespace TauCeti.FormalVertexAxioms

/-! ### State–field correspondence -/

section StateField

variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V] [Module R V]

/-- **State–field correspondence.** For every state `a`, `b` and integer `n : ℤ`, the field of
`a₍ₙ₎ b` is the `n`-th field product `Y(a, z)₍ₙ₎ Y(b, z)`. -/
theorem field_ncoeff_apply (A : FormalVertexAxioms R V) (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  have := HasUniqueDiv.of_algebra_rat R V
  symm
  refine A.eq_field_of_ncoeff_apply_vacuum_eq (fun d ↦ ?_) fun m ↦ ?_
  · obtain ⟨r, hr⟩ := A.exists_isLocalOfOrder a b
    obtain ⟨s, hs⟩ := A.exists_isLocalOfOrder a d
    obtain ⟨t, ht⟩ := A.exists_isLocalOfOrder b d
    exact ⟨_, hr.nthProduct_left hs ht n⟩
  · refine ncoeff_apply_eq_of_lie_eq_derivative A.translation_vacuum
      (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n)
      (A.lie_translation_ncoeff _) ?_ m
    rw [ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
          (A.ncoeff_field_apply_vacuum_of_nonneg b) n,
        A.ncoeff_neg_one_field_apply_vacuum, A.ncoeff_neg_one_field_apply_vacuum]

/-- State–field correspondence for nonnegative residue products (`n : ℕ`). -/
theorem field_ncoeff_natCast_apply (A : FormalVertexAxioms R V) (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  simpa using A.field_ncoeff_apply a b n

/-- State–field correspondence for the normal-ordered product (`n = -1`):
`Y(a₍₋₁₎ b, z) = :Y(a, z) Y(b, z):`. -/
theorem field_ncoeff_neg_one_apply (A : FormalVertexAxioms R V) (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  simpa using A.field_ncoeff_apply a b (-1)

/-- State–field correspondence for negative modes (`n = -k - 1`):
`Y(a₍₋ₖ₋₁₎ b, z) = (k!)⁻¹ : (∂_z^k Y(a, z)) Y(b, z) :`. -/
theorem field_ncoeff_neg_apply (A : FormalVertexAxioms R V) (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-k - 1]]) b) =
      algebraMap ℚ R (k.factorial : ℚ)⁻¹ •
        normalOrder ((derivative (R := R) (V := V))^[k] (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_apply]

end StateField

/-! ### Reconstruction from generating fields -/

section Reconstruction

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The `R`-submodule of fields that are translation-covariant with `T` and mutually local with
every generating field `F j`. -/
private def goodFields (T : Module.End R V) (F : ι → VertexOperator R V) :
    Submodule R (VertexOperator R V) where
  carrier := { B | (∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]]) ∧
    ∀ j : ι, ∃ N : ℕ, B.IsLocalOfOrder (F j) N }
  zero_mem' := ⟨lie_ncoeff_zero T, fun j ↦ ⟨0, IsLocalOfOrder.zero_left (F j) 0⟩⟩
  add_mem' hA hB :=
    ⟨lie_ncoeff_add hA.1 hB.1, fun j ↦ by
      obtain ⟨M, hM⟩ := hA.2 j
      obtain ⟨N, hN⟩ := hB.2 j
      exact ⟨max M N, hM.add_left hN⟩⟩
  smul_mem' r {_} hB :=
    ⟨lie_ncoeff_smul r hB.1, fun j ↦ by
      obtain ⟨N, hN⟩ := hB.2 j
      exact ⟨N, IsLocalOfOrder.smul_left r hN⟩⟩

private theorem id_mem_goodFields (T : Module.End R V) (F : ι → VertexOperator R V) :
    VertexOperator.id ∈ goodFields T F :=
  ⟨lie_ncoeff_id T, fun j ↦ ⟨0, IsLocalOfOrder.id_left (F j) 0⟩⟩

private theorem generator_mem_goodFields {T : Module.End R V} {F : ι → VertexOperator R V}
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N) (i : ι) :
    F i ∈ goodFields T F :=
  ⟨hcov i, hloc i⟩

private theorem derivative_mem_goodFields {T : Module.End R V} {F : ι → VertexOperator R V}
    {B : VertexOperator R V} (hB : B ∈ goodFields T F) :
    derivative B ∈ goodFields T F :=
  ⟨lie_ncoeff_derivative hB.1, fun j ↦ by
    obtain ⟨N, hN⟩ := hB.2 j
    exact ⟨N + 1, hN.derivative_left⟩⟩

/-- Evaluation of a good field on the vacuum at mode `-1`: `B ↦ (B[[-1]]) vac`. -/
private def evalVacuum (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V) :
    goodFields T F →ₗ[R] V where
  toFun B := (B.1[[-1]]) vac
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem evalVacuum_apply (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (B : goodFields T F) :
    evalVacuum vac T F B = (B.1[[-1]]) vac :=
  rfl

variable [Algebra ℚ R]

private theorem nthProduct_generator_mem_goodFields {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (i : ι) (n : ℤ) {B : VertexOperator R V} (hB : B ∈ goodFields T F) :
    nthProduct n (F i) B ∈ goodFields T F :=
  ⟨lie_ncoeff_nthProduct (hcov i) hB.1 n, fun j ↦ by
    obtain ⟨r, hr⟩ := hB.2 i
    obtain ⟨s, hs⟩ := hloc i j
    obtain ⟨t, ht⟩ := hB.2 j
    exact ⟨_, hr.symm.nthProduct_left hs ht n⟩⟩

private theorem evalVacuum_bijective (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    Function.Bijective (evalVacuum vac T F) := by
  have := HasUniqueDiv.of_algebra_rat R V
  refine ⟨fun x y hxy ↦ sub_eq_zero.mp ?_, ?_⟩
  · -- Injectivity: a good field with `(B[[-1]]) vac = 0` kills `vac` in all modes, hence kills `V`.
    let B := (x - y).1
    have hB := (x - y).2
    have hB0 : (B[[-1]]) vac = 0 := by
      simp only [evalVacuum_apply] at hxy
      simp [B, hxy]
    have hBvac : ∀ m : ℤ, (B[[m]]) vac = 0 :=
      ncoeff_apply_eq_zero_of_lie_eq_derivative hT hB.1 hB0
    let W : Submodule R V :=
      { carrier := { v | ∀ m : ℤ, (B[[m]]) v = 0 }
        zero_mem' := fun m ↦ map_zero _
        add_mem' := fun ha hb m ↦ by simp [ha m, hb m]
        smul_mem' := fun r _ ha m ↦ by simp [ha m] }
    have hW : W = ⊤ := hgen W hBvac fun i n v hv m ↦ by
      obtain ⟨N, hN⟩ := hB.2 i
      exact hN.ncoeff_apply_ncoeff_apply_eq_zero hv m n
    ext1
    refine ext_ncoeff fun m ↦ LinearMap.ext fun v ↦ ?_
    exact (Submodule.eq_top_iff'.mp hW v) m
  · -- Surjectivity: `range (evalVacuum vac T F)` contains `vac` and is closed under `(F i)[[n]]`.
    rw [← LinearMap.range_eq_top]
    refine hgen (LinearMap.range (evalVacuum vac T F)) ?_ ?_
    · exact ⟨⟨VertexOperator.id, id_mem_goodFields T F⟩, by simp⟩
    · rintro i n _ ⟨⟨B, hB⟩, rfl⟩
      refine ⟨⟨nthProduct n (F i) B, nthProduct_generator_mem_goodFields hcov hloc i n hB⟩, ?_⟩
      exact ncoeff_neg_one_nthProduct_apply
        (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT (hcov i) hm)
        (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT hB.1 hm) n

/-- The reconstructed linear state–field map `V →ₗ[R] VertexOperator R V`, obtained by inverting
`evalVacuum` onto `goodFields T F`. -/
private def generatingFieldsMap (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    V →ₗ[R] VertexOperator R V :=
  (goodFields T F).subtype.comp
    (LinearEquiv.ofBijective (evalVacuum vac T F)
      (evalVacuum_bijective vac T F hT hcov hloc hgen)).symm.toLinearMap

private theorem generatingFieldsMap_mem_goodFields {vac : V} {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) (a : V) :
    generatingFieldsMap vac T F hT hcov hloc hgen a ∈ goodFields T F := by
  rw [generatingFieldsMap, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_toLinearMap]
  exact Subtype.prop _

private theorem ncoeff_neg_one_generatingFieldsMap_apply_vacuum {vac : V} {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) (a : V) :
    ((generatingFieldsMap vac T F hT hcov hloc hgen a)[[-1]]) vac = a := by
  rw [generatingFieldsMap, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_toLinearMap,
    ← evalVacuum_apply vac T F]
  exact LinearEquiv.apply_ofBijective_symm_apply (evalVacuum vac T F) a

private theorem generatingFieldsMap_ncoeff_neg_one_apply {vac : V} {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    {B : VertexOperator R V} (hB : B ∈ goodFields T F) :
    generatingFieldsMap vac T F hT hcov hloc hgen ((B[[-1]]) vac) = B := by
  have hval : (B[[-1]]) vac = evalVacuum vac T F ⟨B, hB⟩ := (evalVacuum_apply vac T F ⟨B, hB⟩).symm
  rw [hval, generatingFieldsMap, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.ofBijective_symm_apply_apply, Submodule.coe_subtype]

private theorem generatingFieldsMap_vacuum {vac : V} {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    generatingFieldsMap vac T F hT hcov hloc hgen vac = VertexOperator.id := by
  simpa using generatingFieldsMap_ncoeff_neg_one_apply hT hcov hloc hgen (id_mem_goodFields T F)

/-- Any good field `A` is mutually local with every field in the image of `generatingFieldsMap`. -/
private theorem exists_isLocalOfOrder_of_mem_goodFields {vac : V} {T : Module.End R V}
    {F : ι → VertexOperator R V}
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    {A : VertexOperator R V} (hA : A ∈ goodFields T F) (b : V) :
    ∃ N : ℕ, A.IsLocalOfOrder (generatingFieldsMap vac T F hT hcov hloc hgen b) N := by
  have := HasUniqueDiv.of_algebra_rat R V
  let Y := generatingFieldsMap vac T F hT hcov hloc hgen
  let W : Submodule R V :=
    { carrier := { x | ∃ N : ℕ, A.IsLocalOfOrder (Y x) N }
      zero_mem' := ⟨0, by rw [map_zero]; exact IsLocalOfOrder.zero_right A 0⟩
      add_mem' := fun ⟨M, hM⟩ ⟨N, hN⟩ ↦
        ⟨max M N, by rw [map_add]; exact hM.add_right hN⟩
      smul_mem' := fun r x ⟨N, hN⟩ ↦
        ⟨N, by rw [map_smul]; exact IsLocalOfOrder.smul_right r hN⟩ }
  have hW_vac : vac ∈ W :=
    ⟨0, (generatingFieldsMap_vacuum hT hcov hloc hgen) ▸ IsLocalOfOrder.id_right A 0⟩
  have hW_step : ∀ (i : ι) (n : ℤ), ∀ x ∈ W, ((F i)[[n]]) x ∈ W := by
    rintro i n x ⟨t, ht⟩
    have hYx := generatingFieldsMap_mem_goodFields hT hcov hloc hgen x
    have hprod_mem := nthProduct_generator_mem_goodFields hcov hloc i n hYx
    have hprod_eval : ((nthProduct n (F i) (Y x))[[-1]]) vac = ((F i)[[n]]) x := by
      rw [ncoeff_neg_one_nthProduct_apply
            (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT (hcov i) hm)
            (fun _ hm ↦ ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT hYx.1 hm) n,
          ncoeff_neg_one_generatingFieldsMap_apply_vacuum]
    have hY_prod : Y (((F i)[[n]]) x) = nthProduct n (F i) (Y x) := by
      rw [← hprod_eval]
      exact generatingFieldsMap_ncoeff_neg_one_apply hT hcov hloc hgen hprod_mem
    obtain ⟨s, hs⟩ := hA.2 i
    obtain ⟨r, hr⟩ := hYx.2 i
    exact ⟨_, hY_prod ▸ IsLocalOfOrder.nthProduct_right hs ht hr.symm n⟩
  exact Submodule.eq_top_iff'.mp (hgen W hW_vac hW_step) b

/-- **Reconstruction (extension) theorem for formal vertex algebras.** Given a vacuum vector `vac`,
an endomorphism `T` with `T vac = 0`, and a family of pairwise mutually local fields `F i` on an
`R`-module `V` over a `ℚ`-algebra `R` such that `[T, (F i)[[n]]] = (∂(F i))[[n]]` and `V` is
generated as an `R`-submodule from `vac` by the modes `(F i)[[n]]` (`n : ℤ`), there is a canonical
formal vertex algebra structure on `V` with vacuum `vac`, translation `T`, and
`Y(((F i)[[-1]]) vac, z) = F i`. -/
def ofGeneratingFields (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    FormalVertexAxioms R V :=
  have := HasUniqueDiv.of_algebra_rat R V
  { field := generatingFieldsMap vac T F hT hcov hloc hgen
    vacuum := vac
    translation := T
    translation_vacuum := hT
    ncoeff_field_vacuum n := by rw [generatingFieldsMap_vacuum, ncoeff_id]
    ncoeff_field_apply_vacuum_of_nonneg a _ hn :=
      ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT
        (generatingFieldsMap_mem_goodFields hT hcov hloc hgen a).1 hn
    ncoeff_neg_one_field_apply_vacuum :=
      ncoeff_neg_one_generatingFieldsMap_apply_vacuum hT hcov hloc hgen
    field_translation a := by
      have hYa := generatingFieldsMap_mem_goodFields hT hcov hloc hgen a
      have hd_eval :
          ((derivative (generatingFieldsMap vac T F hT hcov hloc hgen a))[[-1]]) vac = T a := by
        rw [← apply_ncoeff_apply_of_lie_eq_derivative hT hYa.1 (-1),
          ncoeff_neg_one_generatingFieldsMap_apply_vacuum]
      rw [← hd_eval]
      exact generatingFieldsMap_ncoeff_neg_one_apply hT hcov hloc hgen
        (derivative_mem_goodFields hYa)
    lie_translation_ncoeff a := (generatingFieldsMap_mem_goodFields hT hcov hloc hgen a).1
    exists_isLocalOfOrder a b :=
      exists_isLocalOfOrder_of_mem_goodFields hT hcov hloc hgen
        (generatingFieldsMap_mem_goodFields hT hcov hloc hgen a) b }

/-- The vacuum of `ofGeneratingFields` is the given vector `vac`. -/
@[simp]
theorem ofGeneratingFields_vacuum (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).vacuum = vac :=
  (rfl)

/-- The translation operator of `ofGeneratingFields` is the given endomorphism `T`. -/
@[simp]
theorem ofGeneratingFields_translation (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).translation = T :=
  (rfl)

/-- The field of `vac` in `ofGeneratingFields` is `VertexOperator.id`. -/
@[simp]
theorem ofGeneratingFields_field_vacuum (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field vac = VertexOperator.id :=
  (ofGeneratingFields vac T F hT hcov hloc hgen).field_vacuum

/-- Reconstructed state–field assignment on the generating states `((F i)[[-1]]) vac`. -/
@[simp]
theorem ofGeneratingFields_field_ncoeff_neg_one_apply (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) (i : ι) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field (((F i)[[-1]]) vac) = F i := by
  rw [ofGeneratingFields]
  exact generatingFieldsMap_ncoeff_neg_one_apply hT hcov hloc hgen
    (generator_mem_goodFields hcov hloc i)

-- `@[simp]` is omitted so it does not collide with `ofGeneratingFields_field_ncoeff_neg_one_apply`
-- at `n = -1`, `v = vac`.
/-- Recursive formula for the reconstructed state–field map under the action of any generator mode
`(F i)[[n]]`. -/
theorem ofGeneratingFields_field_ncoeff_apply (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    (i : ι) (n : ℤ) (v : V) :
    (ofGeneratingFields vac T F hT hcov hloc hgen).field (((F i)[[n]]) v) =
      nthProduct n (F i) ((ofGeneratingFields vac T F hT hcov hloc hgen).field v) := by
  let G := ofGeneratingFields vac T F hT hcov hloc hgen
  have hGi : G.field (((F i)[[-1]]) vac) = F i :=
    ofGeneratingFields_field_ncoeff_neg_one_apply vac T F hT hcov hloc hgen i
  calc
    G.field (((F i)[[n]]) v) = G.field (((G.field (((F i)[[-1]]) vac))[[n]]) v) := by rw [hGi]
    _ = nthProduct n (F i) (G.field v) := by rw [G.field_ncoeff_apply, hGi]

/-- **Extensionality on generating states.** Two formal vertex algebra structures over a `ℚ`-algebra
that share the same vacuum and assign the same fields to a family of states `s : ι → V` whose modes
generate `V` from the vacuum are equal. -/
theorem eq_of_field_eq {A B : FormalVertexAxioms R V} {s : ι → V}
    (hvac : A.vacuum = B.vacuum) (hs : ∀ i : ι, A.field (s i) = B.field (s i))
    (hgen : ∀ W : Submodule R V, A.vacuum ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((A.field (s i))[[n]]) v ∈ W) → W = ⊤) :
    A = B := by
  refine FormalVertexAxioms.ext ?_
  rw [← LinearMap.eqLocus_eq_top]
  refine hgen (LinearMap.eqLocus A.field B.field) ?_ fun i n v hv ↦ ?_
  · rw [LinearMap.mem_eqLocus, A.field_vacuum, hvac, B.field_vacuum]
  · rw [LinearMap.mem_eqLocus] at hv ⊢
    rw [A.field_ncoeff_apply, hv, hs i, B.field_ncoeff_apply]

/-- **Uniqueness in the reconstruction theorem.** Any formal vertex algebra on `V` with vacuum
`vac` whose state–field map assigns `F i` to `((F i)[[-1]]) vac` for each `i` equals
`ofGeneratingFields`. -/
theorem eq_ofGeneratingFields (vac : V) (T : Module.End R V) (F : ι → VertexOperator R V)
    (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤)
    {A : FormalVertexAxioms R V} (hvac : A.vacuum = vac)
    (hF : ∀ i : ι, A.field (((F i)[[-1]]) vac) = F i) :
    A = ofGeneratingFields vac T F hT hcov hloc hgen :=
  eq_of_field_eq (s := fun i ↦ ((F i)[[-1]]) vac) hvac
    (fun i ↦ by rw [hF i, ofGeneratingFields_field_ncoeff_neg_one_apply])
    (fun W hW hstep ↦ hgen W (hvac ▸ hW) fun i n v hv ↦ hF i ▸ hstep i n v hv)

/-- **Existence and uniqueness of the reconstructed formal vertex algebra.** -/
theorem existsUnique_of_generatingFields (vac : V) (T : Module.End R V)
    (F : ι → VertexOperator R V) (hT : T vac = 0)
    (hcov : ∀ (i : ι) (n : ℤ), ⁅T, (F i)[[n]]⁆ = (derivative (F i))[[n]])
    (hloc : ∀ i j : ι, ∃ N : ℕ, (F i).IsLocalOfOrder (F j) N)
    (hgen : ∀ W : Submodule R V, vac ∈ W →
      (∀ (i : ι) (n : ℤ), ∀ v ∈ W, ((F i)[[n]]) v ∈ W) → W = ⊤) :
    ∃! A : FormalVertexAxioms R V,
      A.vacuum = vac ∧ A.translation = T ∧ ∀ i : ι, A.field (((F i)[[-1]]) vac) = F i :=
  ⟨ofGeneratingFields vac T F hT hcov hloc hgen,
    ⟨rfl, rfl, ofGeneratingFields_field_ncoeff_neg_one_apply vac T F hT hcov hloc hgen⟩,
    fun _ ⟨hvac, _, hF⟩ ↦ eq_ofGeneratingFields vac T F hT hcov hloc hgen hvac hF⟩

end Reconstruction

end TauCeti.FormalVertexAxioms
