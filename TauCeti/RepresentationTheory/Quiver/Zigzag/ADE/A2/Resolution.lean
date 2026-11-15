/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.ADE.A2.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Resolution

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

The graph-generic resolution along any degree-one edge is constructed in
`TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Resolution`.  This file specializes it to
the two nodes of `A₂`.  The `n`-th term is `P_{zigzagPeriodicVertex (zigzagA2Dart i) n}` via the
`XIso`, and the `[simp]` lemmas `_complex_d` and `_π_f_zero` identify its differentials and
augmentation.

## Main definitions

* `TauCeti.zigzagA2ProjectiveResolution`: the periodic projective resolution of each simple module
  of the `A₂` zigzag algebra, with its terms identified by
  `TauCeti.zigzagA2ProjectiveResolutionXIso`.

## Main results

* `TauCeti.zigzagA2ProjectiveResolution_complex_d` and
  `TauCeti.zigzagA2ProjectiveResolution_π_f_zero`: the differentials and the augmentation.

## References

* Ruth Stella Huerfano and Mikhail Khovanov, *A category for the adjoint representation*,
  Journal of Algebra 246 (2001), Section 3, for the low-rank zigzag algebras.
* Yuxuan Liu and Ruidong Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg
  algebras*, Section 2, for the `A₂` convention.
-/

open CategoryTheory

public section

namespace TauCeti

universe w

variable (k : Type w) [Field k]

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

/-- The `n`-th term of the resolution of `S_i` is the vertex projective at
`zigzagPeriodicVertex (zigzagA2Dart i) n`. -/
noncomputable def zigzagA2ProjectiveResolutionXIso (i : Fin 2) (n : ℕ) :
    (zigzagA2ProjectiveResolution k i).complex.X n ≅
      ModuleCat.of (nonisolatedZigzagQuotient k zigzagA2Graph)
        (zigzagProjective k zigzagA2Graph (zigzagPeriodicVertex (zigzagA2Dart i) n)) :=
  zigzagPeriodicProjectiveResolutionXIso k _ _ _ _ n

/-- The differentials of the resolution of `S_i` are the maps `zigzagPeriodicDifferential` along
`zigzagA2Dart i`, read through `TauCeti.zigzagA2ProjectiveResolutionXIso`. -/
@[simp]
theorem zigzagA2ProjectiveResolution_complex_d (i : Fin 2) (n : ℕ) :
    (zigzagA2ProjectiveResolution k i).complex.d (n + 1) n =
      (zigzagA2ProjectiveResolutionXIso k i (n + 1)).hom ≫
        ModuleCat.ofHom (zigzagPeriodicDifferential k (zigzagA2Dart i) n) ≫
          (zigzagA2ProjectiveResolutionXIso k i n).inv :=
  zigzagPeriodicProjectiveResolution_complex_d k _ _ _ _ n

/-- The augmentation of the resolution of `S_i` is the head quotient of `P_i`, read through
`TauCeti.zigzagA2ProjectiveResolutionXIso`. -/
@[simp]
theorem zigzagA2ProjectiveResolution_π_f_zero (i : Fin 2) :
    (zigzagA2ProjectiveResolutionXIso k i 0).inv ≫ (zigzagA2ProjectiveResolution k i).π.f 0 =
      ModuleCat.ofHom (zigzagProjectiveToHead k zigzagA2Graph i) :=
  zigzagPeriodicProjectiveResolution_π_f_zero k _ _ _ _

end TauCeti
