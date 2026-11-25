/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.TateEmbedding.Basic
import TauCeti.NumberTheory.NumberField.ComplexEmbedding.Extension

/-!
# Restriction and trace between embedding Tate spaces

Let `E/F` be an extension of fields and `k` a natural number. Complex embeddings of `E` restrict to
complex embeddings of `F`, which gives two real linear maps between the embedding Tate spaces of
`TauCeti.NumberTheory.NumberField.TateEmbedding.Basic`:

* the *restriction* `R : tateEmbeddingSpace F k → tateEmbeddingSpace E k`, `(R v) τ = v (τ|F)`,
  defined more generally along any ring homomorphism `F →+* E`;
* the *trace* `T : tateEmbeddingSpace E k → tateEmbeddingSpace F k`, `(T w) σ = ∑_{τ|F = σ} w τ`,
  summing over all complex embeddings of the number field `E` that extend `σ`.

Both maps preserve the embedding Tate lattices and compose in towers, and since a finite extension
has exactly `[E : F]` complex embeddings over each complex embedding of `F`, `T ∘ R = [E : F]`.
For `k = n - 1` these are the maps of target spaces `Vₙ(F) ⇄ Vₙ(E)` that accompany restriction
and transfer in the algebraic K-theory of number fields under Borel's regulator; the trace is the
embedding sum of Burgos, Definition 10.8.

## Main definitions

* `TauCeti.NumberField.tateEmbeddingRestrict f k`: restriction along `f : F →+* E`.
* `TauCeti.NumberField.tateEmbeddingTrace F E k`: the sum over the embeddings of `E` above each
  embedding of `F`.

## Main results

* `TauCeti.NumberField.tateEmbeddingRestrict_mem_tateEmbeddingLattice`,
  `TauCeti.NumberField.tateEmbeddingTrace_mem_tateEmbeddingLattice`: both maps preserve the
  embedding Tate lattices.
* `TauCeti.NumberField.tateEmbeddingTrace_tateEmbeddingRestrict`: `T (R v) = [E : F] • v`.
* `TauCeti.NumberField.tateEmbeddingRestrict_comp`,
  `TauCeti.NumberField.tateEmbeddingTrace_comp_tateEmbeddingTrace`: restriction and trace compose
  in towers; `TauCeti.NumberField.tateEmbeddingRestrict_id` and
  `TauCeti.NumberField.tateEmbeddingTrace_self` treat the identity extension.

## References

* J. I. Burgos Gil, *The regulators of Beilinson and Borel*, CRM Monograph Series 15, American
  Mathematical Society, 2002, Definition 10.8.
-/

public section

noncomputable section

open NumberField ComplexConjugate Module Finset

namespace TauCeti.NumberField

variable {F E L : Type*} [Field F] [Field E] [Field L]

section Restrict

/-- Restriction along a ring homomorphism `f : F →+* E`: the value of `tateEmbeddingRestrict f k v`
at a complex embedding `τ` of `E` is the value of `v` at `τ ∘ f`. For a field extension `E/F` and
`f = algebraMap F E` this is the restriction map `Vₙ(F) → Vₙ(E)` with `k = n - 1`. -/
def tateEmbeddingRestrict (f : F →+* E) (k : ℕ) :
    tateEmbeddingSpace F k →ₗ[ℝ] tateEmbeddingSpace E k where
  toFun v := ⟨fun τ ↦ (v : (F →+* ℂ) → ℂ) (τ.comp f), mem_tateEmbeddingSpace_iff.mpr
    ⟨fun τ ↦ (mem_tateEmbeddingSpace_iff.mp v.property).1 _, fun τ ↦ by
      simpa only [ComplexEmbedding.conjugate_comp] using
        (mem_tateEmbeddingSpace_iff.mp v.property).2 (τ.comp f)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (f : F →+* E) (g : E →+* L) {k : ℕ}

@[simp]
theorem tateEmbeddingRestrict_apply (v : tateEmbeddingSpace F k) (τ : E →+* ℂ) :
    (tateEmbeddingRestrict f k v : (E →+* ℂ) → ℂ) τ = (v : (F →+* ℂ) → ℂ) (τ.comp f) :=
  (rfl)

@[simp]
theorem tateEmbeddingCoord_tateEmbeddingRestrict (v : tateEmbeddingSpace F k) (τ : E →+* ℂ) :
    tateEmbeddingCoord E k τ (tateEmbeddingRestrict f k v) =
      tateEmbeddingCoord F k (τ.comp f) v := by
  simp [tateEmbeddingCoord_apply]

/-- Restriction maps the embedding Tate lattice of `F` into that of `E`. -/
theorem tateEmbeddingRestrict_mem_tateEmbeddingLattice {v : tateEmbeddingSpace F k}
    (hv : v ∈ tateEmbeddingLattice F k) :
    tateEmbeddingRestrict f k v ∈ tateEmbeddingLattice E k :=
  mem_tateEmbeddingLattice_iff.mpr fun τ ↦ mem_tateEmbeddingLattice_iff.mp hv (τ.comp f)

variable (k) in
/-- Restriction along the identity is the identity. -/
@[simp]
theorem tateEmbeddingRestrict_id :
    tateEmbeddingRestrict (RingHom.id F) k = LinearMap.id := by
  ext v τ
  simp

@[simp]
theorem tateEmbeddingRestrict_tateEmbeddingRestrict (v : tateEmbeddingSpace F k) :
    tateEmbeddingRestrict g k (tateEmbeddingRestrict f k v) =
      tateEmbeddingRestrict (g.comp f) k v :=
  (rfl)

variable (k) in
/-- Restriction along a composite is the composite of the restrictions. -/
theorem tateEmbeddingRestrict_comp :
    tateEmbeddingRestrict (g.comp f) k =
      (tateEmbeddingRestrict g k).comp (tateEmbeddingRestrict f k) :=
  (rfl)

end Restrict

section Trace

variable (F E) [Algebra F E] [NumberField E]

open scoped Classical in
/-- The sum of a function on the complex embeddings of `E` over the embeddings above each complex
embedding of `F`. -/
private def traceFun (w : (E →+* ℂ) → ℂ) (σ : F →+* ℂ) : ℂ :=
  ∑ τ with τ.comp (algebraMap F E) = σ, w τ

variable {F E}

private theorem traceFun_mem {k : ℕ} (w : tateEmbeddingSpace E k) :
    traceFun F E (w : (E →+* ℂ) → ℂ) ∈ tateEmbeddingSpace F k := by
  classical
  obtain ⟨hw₁, hw₂⟩ := mem_tateEmbeddingSpace_iff.mp w.property
  refine mem_tateEmbeddingSpace_iff.mpr ⟨fun σ ↦ ?_, fun σ ↦ ?_⟩
  · choose r hr using hw₁
    exact ⟨∑ τ with τ.comp (algebraMap F E) = σ, r τ, by simp [traceFun, hr, Finset.sum_mul]⟩
  · simp only [traceFun, ComplexEmbedding.sum_filter_comp_algebraMap_eq_conjugate, hw₂, map_sum]

variable (F E) in
/-- The trace from the embedding Tate space of a number field `E` to that of `F`: its value at a
complex embedding `σ` of `F` is the sum of the values at all complex embeddings of `E` extending
`σ`. For `k = n - 1` this is the trace map `Vₙ(E) → Vₙ(F)`. -/
def tateEmbeddingTrace (k : ℕ) : tateEmbeddingSpace E k →ₗ[ℝ] tateEmbeddingSpace F k where
  toFun w := ⟨traceFun F E w, traceFun_mem w⟩
  map_add' w w' := by
    ext σ
    simp [traceFun, Finset.sum_add_distrib]
  map_smul' c w := by
    ext σ
    simp [traceFun, Finset.smul_sum]

variable {k : ℕ}

open scoped Classical in
@[simp]
theorem tateEmbeddingTrace_apply (w : tateEmbeddingSpace E k) (σ : F →+* ℂ) :
    (tateEmbeddingTrace F E k w : (F →+* ℂ) → ℂ) σ =
      ∑ τ with τ.comp (algebraMap F E) = σ, (w : (E →+* ℂ) → ℂ) τ :=
  (rfl)

open scoped Classical in
@[simp]
theorem tateEmbeddingCoord_tateEmbeddingTrace (w : tateEmbeddingSpace E k) (σ : F →+* ℂ) :
    tateEmbeddingCoord F k σ (tateEmbeddingTrace F E k w) =
      ∑ τ with τ.comp (algebraMap F E) = σ, tateEmbeddingCoord E k τ w := by
  simp [tateEmbeddingCoord_apply, tateEmbeddingTrace_apply, Finset.sum_div]

/-- The trace maps the embedding Tate lattice of `E` into that of `F`. -/
theorem tateEmbeddingTrace_mem_tateEmbeddingLattice {w : tateEmbeddingSpace E k}
    (hw : w ∈ tateEmbeddingLattice E k) :
    tateEmbeddingTrace F E k w ∈ tateEmbeddingLattice F k := by
  classical
  choose m hm using mem_tateEmbeddingLattice_iff.mp hw
  refine mem_tateEmbeddingLattice_iff.mpr fun σ ↦ ?_
  exact ⟨∑ τ with τ.comp (algebraMap F E) = σ, m τ,
    by simp [tateEmbeddingTrace_apply, hm, Finset.sum_mul]⟩

/-- The trace of a restriction is multiplication by the degree: `T (R v) = [E : F] • v`. -/
@[simp]
theorem tateEmbeddingTrace_tateEmbeddingRestrict (v : tateEmbeddingSpace F k) :
    tateEmbeddingTrace F E k (tateEmbeddingRestrict (algebraMap F E) k v) = finrank F E • v := by
  classical
  ext σ
  rw [tateEmbeddingTrace_apply, Finset.sum_congr rfl fun τ hτ ↦ by
    rw [tateEmbeddingRestrict_apply, (Finset.mem_filter.mp hτ).2], Finset.sum_const,
    ComplexEmbedding.card_filter_comp_algebraMap_eq]
  simp

variable (F k) in
/-- The trace of the identity extension is the identity. -/
@[simp]
theorem tateEmbeddingTrace_self [NumberField F] : tateEmbeddingTrace F F k = LinearMap.id := by
  classical
  ext w σ
  simp [tateEmbeddingTrace_apply, Finset.sum_filter]

variable [Algebra E L] [Algebra F L] [IsScalarTower F E L] [NumberField L]

/-- The trace in a tower `L/E/F` is the composite of the traces. -/
@[simp]
theorem tateEmbeddingTrace_tateEmbeddingTrace (w : tateEmbeddingSpace L k) :
    tateEmbeddingTrace F E k (tateEmbeddingTrace E L k w) = tateEmbeddingTrace F L k w := by
  classical
  ext σ
  simp [tateEmbeddingTrace_apply, ComplexEmbedding.sum_filter_comp_algebraMap_eq_tower]

variable (F E L k) in
/-- The trace in a tower `L/E/F` is the composite of the traces. -/
theorem tateEmbeddingTrace_comp_tateEmbeddingTrace :
    (tateEmbeddingTrace F E k).comp (tateEmbeddingTrace E L k) = tateEmbeddingTrace F L k :=
  LinearMap.ext tateEmbeddingTrace_tateEmbeddingTrace

end Trace

end TauCeti.NumberField
