/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Order.Directed

/-!
# Graded pieces and strict maps of filtered modules

Let `F : ℤ → Submodule R M` and `G : ℤ → Submodule R N` be increasing filtrations by submodules.
This file records two basic notions of the theory of filtered modules, in the conventions of
Deligne and Saito.

* `TauCeti.GradedPiece F p` is the graded piece `gr^F_p M = F_p M / F_{p-1} M`, and
  `TauCeti.GradedPiece.map u hu p` is the map `gr^F_p M → gr^G_p N` induced by a filtered linear
  map `u`.
* `LinearMap.IsStrict u F G` says that a linear map `u : M → N` is *strict*:
  `u (F_p M) = u M ∩ G_p N` for every `p`. This is the image condition of Deligne
  (*Théorie de Hodge II*, §1.1.5) and Saito (*Modules de Hodge polarisables*, §1.1), used in
  Tau Ceti for mixed Hodge structures in
  `TauCeti.Hodge.MixedHodgeStructure.Hom.range_inf_F_eq_map_F`.
  It differs from Mathlib's `CategoryTheory.FilteredObject.IsStrictHom`, which asks for
  `F_p M = u⁻¹ (G_p N)`; that condition implies this one, but the zero map `M → 0` is strict
  in the present sense for every filtration of `M`, and satisfies the preimage condition only
  when every `F_p M` is all of `M`.

The main result, `LinearMap.isStrict_iff_forall_map_add_one_inf_le`, reduces strictness of a
filtered map, for an exhaustive source filtration, to the one-step condition
`u (F_{p+1} M) ∩ G_p N ⊆ u (F_p M)`. This is the form in which strictness is detected by the
Rees module in `TauCeti.Algebra.Module.Filtration.Rees`.
-/

public section

namespace TauCeti

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The graded piece `gr^F_p M = F_p M / F_{p-1} M` of an increasing filtration by
submodules. -/
abbrev GradedPiece (F : ℤ → Submodule R M) (p : ℤ) : Type _ :=
  F p ⧸ (F (p - 1)).comap (F p).subtype

/-- The class of an element of `F_p M` in `gr^F_p M` vanishes exactly when the element lies in
`F_{p-1} M`. -/
theorem GradedPiece.mk_eq_zero_iff {F : ℤ → Submodule R M} {p : ℤ} (x : F p) :
    (Submodule.Quotient.mk x : GradedPiece F p) = 0 ↔ (x : M) ∈ F (p - 1) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]

variable {N : Type*} [AddCommGroup N] [Module R N] {F : ℤ → Submodule R M}
  {G : ℤ → Submodule R N}

/-- The map `gr^F_p M → gr^G_p N` induced on graded pieces by a linear map `u` sending each
`F_p M` into `G_p N`. -/
noncomputable def GradedPiece.map (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) (p : ℤ) :
    GradedPiece F p →ₗ[R] GradedPiece G p :=
  Submodule.mapQ _ _ (u.restrict fun _ hx ↦ hu p hx) fun _ hx ↦ hu (p - 1) hx

/-- The induced map on graded pieces sends the class of an element to the class of its image. -/
@[simp]
theorem GradedPiece.map_mk (u : M →ₗ[R] N) (hu : ∀ p, F p ≤ (G p).comap u) (p : ℤ) (x : F p) :
    GradedPiece.map u hu p (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨u x, hu p x.property⟩ :=
  (rfl)

/-- The identity induces the identity on graded pieces. -/
@[simp]
theorem GradedPiece.map_id (hu : ∀ p, F p ≤ (F p).comap LinearMap.id := fun _ ↦ le_rfl)
    (p : ℤ) : GradedPiece.map LinearMap.id hu p = LinearMap.id := by
  ext; rfl

/-- The map induced on graded pieces by a composite is the composite of the induced maps. -/
theorem GradedPiece.map_comp {O : Type*} [AddCommGroup O] [Module R O] {H : ℤ → Submodule R O}
    (f : M →ₗ[R] N) (hf : ∀ p, F p ≤ (G p).comap f) (g : N →ₗ[R] O)
    (hg : ∀ p, G p ≤ (H p).comap g)
    (hgf : ∀ p, F p ≤ (H p).comap (g ∘ₗ f) := fun p ↦ (hf p).trans (Submodule.comap_mono (hg p)))
    (p : ℤ) :
    GradedPiece.map (g ∘ₗ f) hgf p = GradedPiece.map g hg p ∘ₗ GradedPiece.map f hf p := by
  ext; rfl

end TauCeti

namespace LinearMap

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A linear map `u : M → N` is *strict* for filtrations `F` of `M` and `G` of `N` when
`u (F_p M) = u M ∩ G_p N` for every index `p`. In particular a strict map sends `F_p M`
into `G_p N`. -/
def IsStrict (u : M →ₗ[R] N) (F : ι → Submodule R M) (G : ι → Submodule R N) : Prop :=
  ∀ p, (F p).map u = range u ⊓ G p

variable {u : M →ₗ[R] N} {F : ι → Submodule R M} {G : ι → Submodule R N}

theorem isStrict_iff : u.IsStrict F G ↔ ∀ p, (F p).map u = range u ⊓ G p := Iff.rfl

/-- A strict map is filtered. -/
theorem IsStrict.le_comap (h : u.IsStrict F G) (p : ι) : F p ≤ (G p).comap u :=
  Submodule.map_le_iff_le_comap.mp ((h p).le.trans inf_le_right)

/-- A filtered map is strict exactly when every element of `G_p N` in its range is the image of
an element of `F_p M`. -/
theorem isStrict_iff_range_inf_le (hu : ∀ p, F p ≤ (G p).comap u) :
    u.IsStrict F G ↔ ∀ p, range u ⊓ G p ≤ (F p).map u := by
  refine ⟨fun h p ↦ (h p).ge, fun h p ↦ le_antisymm ?_ (h p)⟩
  exact le_inf (LinearMap.map_le_range) (Submodule.map_le_iff_le_comap.mpr (hu p))

/-- The identity is strict for a filtration and itself. -/
@[simp]
theorem isStrict_id : (LinearMap.id : M →ₗ[R] M).IsStrict F F := fun p ↦ by
  simp

/-- For `ℤ`-indexed filtrations with `F` exhaustive, strictness of a filtered map `u` can be
checked one step at a time: `u` is strict exactly when every element of `G_p N` that is the image
of an element of `F_{p+1} M` is already the image of an element of `F_p M`. -/
theorem isStrict_iff_forall_map_add_one_inf_le {F : ℤ → Submodule R M} {G : ℤ → Submodule R N}
    (hF : Monotone F) (hG : Monotone G) (hu : ∀ p, F p ≤ (G p).comap u)
    (hex : ⨆ p, F p = ⊤) :
    u.IsStrict F G ↔ ∀ p, (F (p + 1)).map u ⊓ G p ≤ (F p).map u := by
  refine ⟨fun h p ↦ (inf_le_inf_right _ LinearMap.map_le_range).trans (h p).ge, fun h ↦ ?_⟩
  -- Descend from a step containing a preimage to the step `p`, one index at a time.
  have hdesc : ∀ (p : ℤ) (k : ℕ), (F (p + k)).map u ⊓ G p ≤ (F p).map u := by
    intro p k
    induction k with
    | zero => simp
    | succ k ih =>
      refine fun n hn ↦ ih ⟨?_, hn.2⟩
      have hle : G p ≤ G (p + k) := hG (by omega)
      simpa [add_assoc] using h (p + k) ⟨by simpa [add_assoc] using hn.1, hle hn.2⟩
  refine (isStrict_iff_range_inf_le hu).mpr fun p n ⟨⟨m, hm⟩, hn⟩ ↦ ?_
  have hmem : m ∈ ⨆ q, F q := hex ▸ Submodule.mem_top
  obtain ⟨q, hq⟩ := (Submodule.mem_iSup_of_directed F hF.directed_le).mp hmem
  refine hdesc p (q - p).toNat ⟨⟨m, hF (by omega) hq, hm⟩, hn⟩

end LinearMap
