/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.A2.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Syzygy

/-!
# The periodic resolutions of the simple modules of the `A₂` zigzag algebra

The zigzag algebra of `A₂` is the quotient of the path algebra of the doubled quiver
`0 ⇄ 1` by all paths of length three.  It is not quadratic, and its simple modules have the
explicit projective resolutions

```text
⋯ ⟶ P₁ --x₁--> P₁ --a--> P₀ --x₀--> P₀ --b--> P₁ --x₁--> P₁ --a--> P₀ ⟶ S₀ ⟶ 0,
```

periodic of period four, where `a : 0 → 1` and `b : 1 → 0` are the two arrows, `x₀` and `x₁`
are the volume classes, and each map is right multiplication by the displayed element.  The
differentials alternate between path degree one and path degree two, so this resolution is not
linear; it is the explicit resolution with which `A₂` is treated in place of a Koszul resolution.

Exactness only uses that both ends of the edge have degree one, so the resolution is constructed
for the simple head `P_i / J P_i` at the tail `i` of a dart `d` of any finite graph without
isolated vertices, provided both endpoints of `d` have degree one (that is, `d` spans a connected
component isomorphic to `A₂`).  At every vertex the image of each map is the kernel of the next
by the computations of `TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Syzygy`:

* `x_j : P_j → P_j` has image `J² P_j` and kernel `J P_j`;
* the arrow `P_{d.snd} → P_{d.fst}` has image `J P_{d.fst}` and kernel `J² P_{d.snd}`.

The construction follows the formal precedent `TauCeti.dualNumberProjectiveResolution` in
`TauCeti.Algebra.Homology.Ext.DualNumbers`: a private periodic complex with a separate
augmentation built through `ChainComplex.toSingle₀Equiv`, the same proof of `quasiIso`, terms
identified by an `XIso` given by `Iso.refl`, and characterising lemmas for the differentials and
the augmentation.

## Main definitions

* `TauCeti.zigzagPeriodicVertex`: the vertices `d.fst, d.snd, d.snd, d.fst, …` of the terms.
* `TauCeti.zigzagPeriodicDifferential`: the differentials, alternating arrows and volumes.
* `TauCeti.zigzagPeriodicProjectiveResolution`: the periodic projective resolution of the simple
  head at the tail of an edge whose endpoints have degree one, with its terms identified by
  `TauCeti.zigzagPeriodicProjectiveResolutionXIso`.
* `TauCeti.zigzagA2ProjectiveResolution`: the periodic projective resolution of each simple module
  of the `A₂` zigzag algebra.

## Main results

* `TauCeti.range_zigzagPeriodicDifferential_succ`: exactness of the periodic complex.
* `TauCeti.zigzagPeriodicProjectiveResolution_complex_d` and
  `TauCeti.zigzagPeriodicProjectiveResolution_π_f_zero`: the differentials and the augmentation.

## References

* Ruth Stella Huerfano and Mikhail Khovanov, *A category for the adjoint representation*,
  Journal of Algebra 246 (2001), Section 3, for the low-rank zigzag algebras.
* Yuxuan Liu and Ruidong Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg
  algebras*, Section 2, for the `A₂` convention.
-/

open CategoryTheory

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} {G : SimpleGraph V}

local notation "Z" => nonisolatedZigzagQuotient k G

/-! ### The periodic complex -/

/-- The vertices of the terms of the periodic resolution along a dart `d`: the sequence
`d.fst, d.snd, d.snd, d.fst`, repeated with period four. -/
@[expose]
def zigzagPeriodicVertex (d : G.Dart) : ℕ → V
  | 0 => d.fst
  | 1 => d.snd
  | 2 => d.snd
  | 3 => d.fst
  | n + 4 => zigzagPeriodicVertex d n

@[simp]
theorem zigzagPeriodicVertex_zero (d : G.Dart) : zigzagPeriodicVertex d 0 = d.fst := (rfl)

@[simp]
theorem zigzagPeriodicVertex_one (d : G.Dart) : zigzagPeriodicVertex d 1 = d.snd := (rfl)

@[simp]
theorem zigzagPeriodicVertex_two (d : G.Dart) : zigzagPeriodicVertex d 2 = d.snd := (rfl)

@[simp]
theorem zigzagPeriodicVertex_three (d : G.Dart) : zigzagPeriodicVertex d 3 = d.fst := (rfl)

@[simp]
theorem zigzagPeriodicVertex_add_four (d : G.Dart) (n : ℕ) :
    zigzagPeriodicVertex d (n + 4) = zigzagPeriodicVertex d n := (rfl)

variable [Finite V]

/-- The differentials of the periodic resolution along a dart `d`: right multiplication by the
arrow of `d`, the volume at `d.snd`, the arrow of the reverse dart and the volume at `d.fst`,
repeated with period four. -/
noncomputable def zigzagPeriodicDifferential (d : G.Dart) : ∀ n : ℕ,
    zigzagProjective k G (zigzagPeriodicVertex d (n + 1)) →ₗ[Z]
      zigzagProjective k G (zigzagPeriodicVertex d n)
  | 0 => zigzagProjectiveArrowMul k G d
  | 1 => zigzagProjectiveVolumeMul k G d.snd
  | 2 => zigzagProjectiveArrowMul k G d.symm
  | 3 => zigzagProjectiveVolumeMul k G d.fst
  | n + 4 => zigzagPeriodicDifferential d n

@[simp]
theorem zigzagPeriodicDifferential_zero (d : G.Dart) :
    zigzagPeriodicDifferential k d 0 = zigzagProjectiveArrowMul k G d := (rfl)

@[simp]
theorem zigzagPeriodicDifferential_one (d : G.Dart) :
    zigzagPeriodicDifferential k d 1 = zigzagProjectiveVolumeMul k G d.snd := (rfl)

@[simp]
theorem zigzagPeriodicDifferential_two (d : G.Dart) :
    zigzagPeriodicDifferential k d 2 = zigzagProjectiveArrowMul k G d.symm := (rfl)

@[simp]
theorem zigzagPeriodicDifferential_three (d : G.Dart) :
    zigzagPeriodicDifferential k d 3 = zigzagProjectiveVolumeMul k G d.fst := (rfl)

@[simp]
theorem zigzagPeriodicDifferential_add_four (d : G.Dart) (n : ℕ) :
    zigzagPeriodicDifferential k d (n + 4) = zigzagPeriodicDifferential k d n := (rfl)

/-- Consecutive differentials compose to zero: a volume class times an arrow, and an arrow
times a volume class, have path length three. -/
theorem zigzagPeriodicDifferential_comp_succ (d : G.Dart) : ∀ n : ℕ,
    zigzagPeriodicDifferential k d n ∘ₗ zigzagPeriodicDifferential k d (n + 1) = 0
  | 0 => zigzagProjectiveArrowMul_comp_zigzagProjectiveVolumeMul k G d
  | 1 => zigzagProjectiveVolumeMul_comp_zigzagProjectiveArrowMul k G d.symm
  | 2 => zigzagProjectiveArrowMul_comp_zigzagProjectiveVolumeMul k G d.symm
  | 3 => zigzagProjectiveVolumeMul_comp_zigzagProjectiveArrowMul k G d
  | n + 4 => zigzagPeriodicDifferential_comp_succ d n

/-- The periodic complex of vertex projectives along a dart `d`, before augmentation. -/
private noncomputable def zigzagPeriodicComplex (d : G.Dart) : ChainComplex (ModuleCat Z) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of Z (zigzagProjective k G (zigzagPeriodicVertex d n)))
    (fun n => ModuleCat.ofHom (zigzagPeriodicDifferential k d n))
    (fun n => ModuleCat.hom_ext (by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom,
        zigzagPeriodicDifferential_comp_succ, ModuleCat.hom_zero]))

private theorem zigzagPeriodicComplex_d (d : G.Dart) (n : ℕ) :
    (zigzagPeriodicComplex k d).d (n + 1) n =
      ModuleCat.ofHom (zigzagPeriodicDifferential k d n) :=
  ChainComplex.of_d (fun n => ModuleCat.of Z (zigzagProjective k G (zigzagPeriodicVertex d n)))
    (fun n => ModuleCat.ofHom (zigzagPeriodicDifferential k d n)) n

/-! ### The augmentation and the resolution -/

/-- The augmentation of the periodic complex onto the simple head `P_{d.fst} / J P_{d.fst}`. -/
private noncomputable def zigzagPeriodicComplexπ (hns : ∀ i : V, ∃ j, G.Adj i j)
    (d : G.Dart) :
    zigzagPeriodicComplex k d ⟶ (ChainComplex.single₀ (ModuleCat Z)).obj
      (ModuleCat.of Z (zigzagProjectiveRadicalLayer k G d.fst 0)) :=
  ((zigzagPeriodicComplex k d).toSingle₀Equiv _).symm
    ⟨ModuleCat.ofHom (zigzagProjectiveToHead k G d.fst), by
      rw [zigzagPeriodicComplex_d]
      exact ModuleCat.hom_ext (zigzagProjectiveToHead_comp_zigzagProjectiveArrowMul hns d)⟩

private theorem zigzagPeriodicComplexπ_f_zero (hns : ∀ i : V, ∃ j, G.Adj i j) (d : G.Dart) :
    (zigzagPeriodicComplexπ k hns d).f 0 = ModuleCat.ofHom (zigzagProjectiveToHead k G d.fst) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable [Fintype V] [DecidableRel G.Adj]

/-- **Exactness of the periodic complex.** If both endpoints of `d` have degree one, the image of
each differential is the kernel of the previous one. -/
theorem range_zigzagPeriodicDifferential_succ (hns : ∀ i : V, ∃ j, G.Adj i j) (d : G.Dart)
    (hfst : G.degree d.fst = 1) (hsnd : G.degree d.snd = 1) : ∀ n : ℕ,
    LinearMap.range (zigzagPeriodicDifferential k d (n + 1)) =
      LinearMap.ker (zigzagPeriodicDifferential k d n)
  | 0 => (range_zigzagProjectiveVolumeMul hns d.snd).trans
      (ker_zigzagProjectiveArrowMul hns d hsnd).symm
  | 1 => (range_zigzagProjectiveArrowMul hns d.symm hsnd).trans
      (ker_zigzagProjectiveVolumeMul hns d.snd).symm
  | 2 => (range_zigzagProjectiveVolumeMul hns d.fst).trans
      (ker_zigzagProjectiveArrowMul hns d.symm hfst).symm
  | 3 => (range_zigzagProjectiveArrowMul hns d hfst).trans
      (ker_zigzagProjectiveVolumeMul hns d.fst).symm
  | n + 4 => range_zigzagPeriodicDifferential_succ hns d hfst hsnd n

/-- **The periodic projective resolution along an `A₂` component.** Let `d` be a dart of a finite
graph without isolated vertices whose two endpoints both have degree one.  Then the simple head
`S = P_{d.fst} / J P_{d.fst}` has the projective resolution

`⋯ ⟶ P_{d.snd} --x--> P_{d.snd} --a_d--> P_{d.fst} ⟶ S ⟶ 0`

with terms `P_{d.fst}, P_{d.snd}, P_{d.snd}, P_{d.fst}, …` and differentials right
multiplication by `a_d`, `x_{d.snd}`, `a_{d.symm}` and `x_{d.fst}`, repeated with period four. -/
noncomputable def zigzagPeriodicProjectiveResolution (hns : ∀ i : V, ∃ j, G.Adj i j)
    (d : G.Dart) (hfst : G.degree d.fst = 1) (hsnd : G.degree d.snd = 1) :
    ProjectiveResolution (ModuleCat.of Z (zigzagProjectiveRadicalLayer k G d.fst 0)) where
  complex := zigzagPeriodicComplex k d
  projective n :=
    have := zigzagProjective_projective k G (zigzagPeriodicVertex d n)
    inferInstanceAs (Projective (ModuleCat.of Z (zigzagProjective k G (zigzagPeriodicVertex d n))))
  π := zigzagPeriodicComplexπ k hns d
  quasiIso := by
    constructor
    intro m
    cases m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simp only [zigzagPeriodicComplex_d, HomologicalComplex.shortComplexFunctor'_obj_f]
        -- the remaining map is the augmentation in degree zero, the head quotient by definition
        exact (range_zigzagProjectiveArrowMul (k := k) hns d hfst).trans
          (ker_zigzagProjectiveToHead d.fst).symm
      · rw [ModuleCat.epi_iff_surjective]
        exact zigzagProjectiveToHead_surjective k G d.fst
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp),
        ShortComplex.moduleCat_exact_iff_range_eq_ker]
      simp only [zigzagPeriodicComplex_d, HomologicalComplex.shortComplexFunctor'_obj_f,
        HomologicalComplex.shortComplexFunctor'_obj_g]
      exact range_zigzagPeriodicDifferential_succ k hns d hfst hsnd m

/-- The `n`-th term of the periodic resolution is the vertex projective at
`zigzagPeriodicVertex d n`. -/
noncomputable def zigzagPeriodicProjectiveResolutionXIso (hns : ∀ i : V, ∃ j, G.Adj i j)
    (d : G.Dart) (hfst : G.degree d.fst = 1) (hsnd : G.degree d.snd = 1) (n : ℕ) :
    (zigzagPeriodicProjectiveResolution k hns d hfst hsnd).complex.X n ≅
      ModuleCat.of Z (zigzagProjective k G (zigzagPeriodicVertex d n)) :=
  Iso.refl _

/-- The differentials of the periodic resolution are the maps `zigzagPeriodicDifferential`, read
through `TauCeti.zigzagPeriodicProjectiveResolutionXIso`. -/
@[simp]
theorem zigzagPeriodicProjectiveResolution_complex_d (hns : ∀ i : V, ∃ j, G.Adj i j)
    (d : G.Dart) (hfst : G.degree d.fst = 1) (hsnd : G.degree d.snd = 1) (n : ℕ) :
    (zigzagPeriodicProjectiveResolution k hns d hfst hsnd).complex.d (n + 1) n =
      (zigzagPeriodicProjectiveResolutionXIso k hns d hfst hsnd (n + 1)).hom ≫
        ModuleCat.ofHom (zigzagPeriodicDifferential k d n) ≫
          (zigzagPeriodicProjectiveResolutionXIso k hns d hfst hsnd n).inv :=
  -- the two isomorphisms are identities, so the right-hand side is the differential itself
  zigzagPeriodicComplex_d k d n

/-- The augmentation of the periodic resolution is the head quotient of `P_{d.fst}`, read through
`TauCeti.zigzagPeriodicProjectiveResolutionXIso`. -/
@[simp]
theorem zigzagPeriodicProjectiveResolution_π_f_zero (hns : ∀ i : V, ∃ j, G.Adj i j)
    (d : G.Dart) (hfst : G.degree d.fst = 1) (hsnd : G.degree d.snd = 1) :
    (zigzagPeriodicProjectiveResolutionXIso k hns d hfst hsnd 0).inv ≫
        (zigzagPeriodicProjectiveResolution k hns d hfst hsnd).π.f 0 =
      ModuleCat.ofHom (zigzagProjectiveToHead k G d.fst) :=
  -- the isomorphism is an identity, so the left-hand side is the augmentation itself
  zigzagPeriodicComplexπ_f_zero k hns d

/-! ### The zigzag algebra of `A₂` -/

/-- The dart of `A₂` leaving the node `i`. -/
def zigzagA2Dart (i : Fin 2) : zigzagA2Graph.Dart :=
  ⟨(i, i + 1), by fin_cases i <;> simp⟩

@[simp]
theorem zigzagA2Dart_fst (i : Fin 2) : (zigzagA2Dart i).fst = i := (rfl)

@[simp]
theorem zigzagA2Dart_snd (i : Fin 2) : (zigzagA2Dart i).snd = i + 1 := (rfl)

/-- Both nodes of `A₂` have degree one. -/
theorem degree_zigzagA2Graph (i : Fin 2) : zigzagA2Graph.degree i = 1 := by
  fin_cases i <;> decide

/-- **The periodic projective resolution of a simple module of the `A₂` zigzag algebra.** The
simple head `S_i = P_i / J P_i` at the node `i` has the period-four projective resolution

`⋯ ⟶ P_{i+1} --x_{i+1}--> P_{i+1} --a--> P_i ⟶ S_i ⟶ 0`

with terms `P_i, P_{i+1}, P_{i+1}, P_i, …`, whose differentials are right multiplication by the
arrow `i → i + 1`, the volume at `i + 1`, the arrow `i + 1 → i` and the volume at `i`. -/
noncomputable def zigzagA2ProjectiveResolution (i : Fin 2) :
    ProjectiveResolution (ModuleCat.of (nonisolatedZigzagQuotient k zigzagA2Graph)
      (zigzagProjectiveRadicalLayer k zigzagA2Graph i 0)) :=
  zigzagPeriodicProjectiveResolution k exists_adj_zigzagA2Graph (zigzagA2Dart i)
    (degree_zigzagA2Graph i) (degree_zigzagA2Graph (i + 1))

end TauCeti
