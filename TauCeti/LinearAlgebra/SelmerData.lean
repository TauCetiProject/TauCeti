/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Selmer data over a ring and their Selmer modules

**Selmer data** over a semiring `R`, indexed by a type `ι` of places, consist of a global
`R`-module `H`, local `R`-modules `Hloc v`, `R`-linear localisation maps `res_v : H → Hloc v`,
and local conditions `L_v ≤ Hloc v`. Their **Selmer module** is

```text
Sel(D) = {c ∈ H | ∀ v, res_v c ∈ L_v} = ker(H → ∏_v Hloc v ⧸ L_v).
```

In the arithmetic applications `H = H¹(G_{K,Σ}, M)` and `Hloc v = H¹(K_v, M)` for discrete,
compact lattice or rational coefficients `M`, and `R` is the coefficient ring. Only the
module-theoretic diagram enters here. The discrete Selmer structures of
`TauCeti.ContCohomology.SelmerStructure` are an instance over `ℤ`
(`TauCeti.ContCohomology.SelmerStructure.toSelmerData`).

The local conditions can be modified on a set of places: relaxed (`L_v = Hloc v`) on `B` and
strict (`L_v = 0`) on `A`. Mazur–Rubin's `F^b_a` is `(D.strict a).relax b`, and Rubin's `S^Σ`
and `S_Σ` are `D.relax Σ` and `D.strict Σ`. The localisation is a product over all places: for
compact or rational coefficients a single global class can have infinitely many nonzero singular
localisations, so no restricted product is used.

## Main definitions

* `TauCeti.SelmerData`: localisation maps and local conditions.
* `TauCeti.SelmerData.selmerModule`: the Selmer module, the intersection of the preimages of
  the local conditions.
* `TauCeti.SelmerData.withLocalConditions`: replace the local conditions.
* `TauCeti.SelmerData.relax`, `TauCeti.SelmerData.strict`: relaxed and strict conditions on a set
  of places.
* `TauCeti.SelmerData.singularLocalization`: the map `H → ∏_v Hloc v ⧸ L_v`.

## Main results

* `TauCeti.SelmerData.mem_selmerModule_iff`: a class is Selmer exactly when every localisation
  satisfies the local condition.
* `TauCeti.SelmerData.ker_singularLocalization`: the Selmer module is the kernel of
  `H → ∏_v Hloc v ⧸ L_v`.
* `TauCeti.SelmerData.selmerModule_withLocalConditions_mono`: the Selmer module is monotone in the
  local conditions.
* `TauCeti.SelmerData.selmerModule_strict_le`, `TauCeti.SelmerData.le_selmerModule_relax`:
  `Sel_strict ≤ Sel ≤ Sel_relaxed`.
* `TauCeti.SelmerData.selmerModule_relax_univ`,
  `TauCeti.SelmerData.selmerModule_strict_univ`, `TauCeti.SelmerData.selmerModule_of_isEmpty`:
  relaxing everywhere gives `H`, imposing strict conditions everywhere gives `⋂_v ker res_v`, and
  with no places the Selmer module is `H`.

## References

* B. Mazur and K. Rubin, *Kolyvagin systems*, Mem. Amer. Math. Soc. 168 (2004), arXiv v1,
  Definition 1.1 and Definition 2.1.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.5, Definition 5.1.
-/

public section

namespace TauCeti

section Semiring

variable (R : Type*) [Semiring R] (ι : Type*) (H : Type*) [AddCommMonoid H] [Module R H]
  (Hloc : ι → Type*) [∀ v, AddCommMonoid (Hloc v)] [∀ v, Module R (Hloc v)]

/-- **Selmer data** over `R` indexed by the places `ι`: an `R`-linear localisation map from the
global module `H` to the local module `Hloc v` at each place, and a local condition, an
`R`-submodule of `Hloc v`. -/
@[ext]
structure SelmerData where
  /-- The localisation map `res_v : H → Hloc v`. -/
  localization : ∀ v, H →ₗ[R] Hloc v
  /-- The local condition `L_v`, a submodule of `Hloc v`. -/
  localCondition : ∀ v, Submodule R (Hloc v)

namespace SelmerData

variable {R ι H Hloc} (D : SelmerData R ι H Hloc)

/-! ### The Selmer module -/

/-- **The Selmer module** of Selmer data: the classes of `H` whose localisation at every place
lies in the local condition. -/
def selmerModule : Submodule R H :=
  ⨅ v, (D.localCondition v).comap (D.localization v)

/-- The Selmer module is the intersection of the preimages of the local conditions. -/
theorem selmerModule_def :
    D.selmerModule = ⨅ v, (D.localCondition v).comap (D.localization v) :=
  (rfl)

/-- A class is Selmer exactly when its localisation at every place satisfies the local
condition. -/
@[simp]
theorem mem_selmerModule_iff {c : H} :
    c ∈ D.selmerModule ↔ ∀ v, D.localization v c ∈ D.localCondition v := by
  simp only [selmerModule, Submodule.mem_iInf, Submodule.mem_comap]

/-- Every localisation of a Selmer class satisfies the corresponding local condition. -/
theorem localization_mem (c : D.selmerModule) (v : ι) :
    D.localization v c ∈ D.localCondition v :=
  D.mem_selmerModule_iff.mp c.property v

/-- The Selmer module is everything when every local condition is everything. -/
theorem selmerModule_eq_top (h : ∀ v, D.localCondition v = ⊤) : D.selmerModule = ⊤ := by
  simp [selmerModule, h]

/-- With no places the Selmer module is the whole global module. -/
@[simp]
theorem selmerModule_of_isEmpty [IsEmpty ι] : D.selmerModule = ⊤ :=
  D.selmerModule_eq_top isEmptyElim

/-- When every local condition is zero, the Selmer module is `⋂_v ker res_v`. -/
theorem selmerModule_eq_iInf_ker (h : ∀ v, D.localCondition v = ⊥) :
    D.selmerModule = ⨅ v, LinearMap.ker (D.localization v) := by
  simp only [selmerModule, h, Submodule.comap_bot]

/-! ### Replacing the local conditions -/

/-- Replace the local conditions of Selmer data, keeping the localisation maps. -/
def withLocalConditions (L : ∀ v, Submodule R (Hloc v)) : SelmerData R ι H Hloc :=
  { D with localCondition := L }

/-- Replacing the local conditions keeps the localisation maps. -/
@[simp]
theorem withLocalConditions_localization (L : ∀ v, Submodule R (Hloc v)) :
    (D.withLocalConditions L).localization = D.localization :=
  (rfl)

/-- The replaced Selmer data have the prescribed local conditions. -/
@[simp]
theorem withLocalConditions_localCondition (L : ∀ v, Submodule R (Hloc v)) :
    (D.withLocalConditions L).localCondition = L :=
  (rfl)

/-- The Selmer module is monotone in the local conditions. -/
theorem selmerModule_withLocalConditions_mono :
    Monotone fun L : ∀ v, Submodule R (Hloc v) => (D.withLocalConditions L).selmerModule :=
  fun _ _ hLL' => iInf_mono fun v => Submodule.comap_mono (hLL' v)

/-- Enlarging every local condition enlarges the Selmer module. -/
theorem selmerModule_le_withLocalConditions {L : ∀ v, Submodule R (Hloc v)}
    (h : ∀ v, D.localCondition v ≤ L v) :
    D.selmerModule ≤ (D.withLocalConditions L).selmerModule :=
  iInf_mono fun v => Submodule.comap_mono (h v)

/-! ### Relaxed and strict conditions on a set of places -/

/-- Relax the local conditions on the places of `B`: the condition at `v ∈ B` becomes the whole
local module, and the others are unchanged. -/
def relax (B : Set ι) : SelmerData R ι H Hloc :=
  D.withLocalConditions fun v => D.localCondition v ⊔ ⨆ _ : v ∈ B, ⊤

/-- Impose the strict condition on the places of `A`: the condition at `v ∈ A` becomes zero, and
the others are unchanged. -/
def strict (A : Set ι) : SelmerData R ι H Hloc :=
  D.withLocalConditions fun v => D.localCondition v ⊓ ⨅ _ : v ∈ A, ⊥

/-- Relaxing conditions keeps the localisation maps. -/
@[simp]
theorem relax_localization (B : Set ι) : (D.relax B).localization = D.localization :=
  (rfl)

/-- Imposing strict conditions keeps the localisation maps. -/
@[simp]
theorem strict_localization (A : Set ι) : (D.strict A).localization = D.localization :=
  (rfl)

/-- The relaxed condition at `v` is `L_v` enlarged to everything when `v ∈ B`. -/
theorem relax_localCondition (B : Set ι) (v : ι) :
    (D.relax B).localCondition v = D.localCondition v ⊔ ⨆ _ : v ∈ B, ⊤ :=
  (rfl)

/-- The strict condition at `v` is `L_v` cut down to zero when `v ∈ A`. -/
theorem strict_localCondition (A : Set ι) (v : ι) :
    (D.strict A).localCondition v = D.localCondition v ⊓ ⨅ _ : v ∈ A, ⊥ :=
  (rfl)

/-- At a relaxed place the local condition is the whole local module. -/
@[simp]
theorem relax_localCondition_of_mem {B : Set ι} {v : ι} (hv : v ∈ B) :
    (D.relax B).localCondition v = ⊤ := by
  simp [relax, hv]

/-- Away from the relaxed places the local condition is unchanged. -/
@[simp]
theorem relax_localCondition_of_notMem {B : Set ι} {v : ι} (hv : v ∉ B) :
    (D.relax B).localCondition v = D.localCondition v := by
  simp [relax, hv]

/-- At a strict place the local condition is zero. -/
@[simp]
theorem strict_localCondition_of_mem {A : Set ι} {v : ι} (hv : v ∈ A) :
    (D.strict A).localCondition v = ⊥ := by
  simp [strict, hv]

/-- Away from the strict places the local condition is unchanged. -/
@[simp]
theorem strict_localCondition_of_notMem {A : Set ι} {v : ι} (hv : v ∉ A) :
    (D.strict A).localCondition v = D.localCondition v := by
  simp [strict, hv]

/-- Relaxing conditions enlarges the Selmer module. -/
theorem le_selmerModule_relax (B : Set ι) : D.selmerModule ≤ (D.relax B).selmerModule :=
  D.selmerModule_le_withLocalConditions fun _ => le_sup_left

/-- Imposing strict conditions shrinks the Selmer module. -/
theorem selmerModule_strict_le (A : Set ι) : (D.strict A).selmerModule ≤ D.selmerModule :=
  (D.strict A).selmerModule_le_withLocalConditions (L := D.localCondition) fun _ => inf_le_left

/-- `Sel_strict ≤ Sel_relaxed`. -/
theorem selmerModule_strict_le_relax (A B : Set ι) :
    (D.strict A).selmerModule ≤ (D.relax B).selmerModule :=
  (D.selmerModule_strict_le A).trans (D.le_selmerModule_relax B)

/-- Relaxing the conditions at every place gives the whole global module. -/
@[simp]
theorem selmerModule_relax_univ : (D.relax Set.univ).selmerModule = ⊤ :=
  (D.relax Set.univ).selmerModule_eq_top fun _ => D.relax_localCondition_of_mem (Set.mem_univ _)

/-- Imposing the strict condition at every place gives `⋂_v ker res_v`. -/
@[simp]
theorem selmerModule_strict_univ :
    (D.strict Set.univ).selmerModule = ⨅ v, LinearMap.ker (D.localization v) :=
  (D.strict Set.univ).selmerModule_eq_iInf_ker fun _ =>
    D.strict_localCondition_of_mem (Set.mem_univ _)

/-- Relaxing on no places changes nothing. -/
@[simp]
theorem relax_empty : D.relax ∅ = D := by
  simp [relax, withLocalConditions]

/-- Imposing strict conditions on no places changes nothing. -/
@[simp]
theorem strict_empty : D.strict ∅ = D := by
  simp [strict, withLocalConditions]

end SelmerData

end Semiring

section Ring

variable {R : Type*} [Ring R] {ι : Type*} {H : Type*} [AddCommGroup H] [Module R H]
  {Hloc : ι → Type*} [∀ v, AddCommGroup (Hloc v)] [∀ v, Module R (Hloc v)]
  (D : SelmerData R ι H Hloc)

namespace SelmerData

/-! ### The Selmer module as a kernel -/

/-- **The singular localisation** `H → ∏_v Hloc v ⧸ L_v`: localise at every place and reduce
modulo the local condition. -/
def singularLocalization : H →ₗ[R] ∀ v, Hloc v ⧸ D.localCondition v :=
  LinearMap.pi fun v => (D.localCondition v).mkQ ∘ₗ D.localization v

/-- The component at `v` of the singular localisation is `res_v c` modulo `L_v`. -/
@[simp]
theorem singularLocalization_apply (c : H) (v : ι) :
    D.singularLocalization c v = Submodule.Quotient.mk (D.localization v c) :=
  (rfl)

/-- **The Selmer module is the kernel of the singular localisation**
`H → ∏_v Hloc v ⧸ L_v`. -/
@[simp]
theorem ker_singularLocalization : LinearMap.ker D.singularLocalization = D.selmerModule := by
  ext c
  simp [funext_iff, Submodule.Quotient.mk_eq_zero]

end SelmerData

end Ring

end TauCeti
