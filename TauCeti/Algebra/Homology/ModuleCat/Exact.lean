/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Exact sequences of cycles, opcycles and homology of complexes of modules

For a homological complex `K` of modules and `c.Rel i j`, the cycles `Zᵢ = ker dᵢ`, the
opcycles `Kᵢ / Bᵢ = coker dᵢ₋₁` and the homology fit into the exact sequences

`0 → Zᵢ → Kᵢ → Kⱼ` and `Kᵢ → Kⱼ → Kⱼ / Bⱼ → 0`,

which present the cycles as a kernel and the opcycles as a cokernel, and the four-term exact
sequence

`0 → Hᵢ → Kᵢ / Bᵢ → Zⱼ → Hⱼ → 0`

of Mathlib's `HomologicalComplex.HomologySequence.composableArrows₃`, whose middle map is induced
by the differential `dᵢⱼ`. This file states them for the underlying linear maps, as
`Function.Exact`, injectivity and surjectivity, which is the form in which exact sequences of
vector spaces are fed to the determinant lines of `TauCeti.LinearAlgebra.Determinant.Exact`.

On elements, the class in the opcycles of a cycle is the image of its homology class, and the
middle map sends the class of `x` to the cycle `dᵢⱼ x`
(`HomologicalComplex.moduleCat_homologyι_homologyπ_apply`,
`HomologicalComplex.moduleCat_opcyclesToCycles_pOpcycles_apply`).

The cycles, opcycles and homology of a complex of finitely generated modules over a Noetherian
ring are finitely generated (`HomologicalComplex.moduleFinite_cycles`,
`HomologicalComplex.moduleFinite_opcycles`, `HomologicalComplex.moduleFinite_homology`).

## Main results

* `HomologicalComplex.moduleCat_exact_iCycles_d`: `Zᵢ → Kᵢ → Kⱼ` is exact.
* `HomologicalComplex.moduleCat_exact_d_pOpcycles`: `Kᵢ → Kⱼ → Kⱼ / Bⱼ` is exact.
* `HomologicalComplex.moduleCat_exact_homologyι_opcyclesToCycles`,
  `HomologicalComplex.moduleCat_exact_opcyclesToCycles_homologyπ`: exactness of
  `Hᵢ → Kᵢ / Bᵢ → Zⱼ → Hⱼ` at its two middle terms.
-/

public section

open CategoryTheory

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c)

/-- The cycles of degree `i` are the kernel of the differential `dᵢⱼ`: the sequence
`Zᵢ → Kᵢ → Kⱼ` is exact. -/
lemma moduleCat_exact_iCycles_d {i j : ι} (hij : c.next i = j) :
    Function.Exact (K.iCycles i).hom (K.d i j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j))).1
    (ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j hij))

/-- The opcycles of degree `j` are the cokernel of the differential `dᵢⱼ`: the sequence
`Kᵢ → Kⱼ → Kⱼ / Bⱼ` is exact. -/
lemma moduleCat_exact_d_pOpcycles {i j : ι} (hij : c.prev j = i) :
    Function.Exact (K.d i j).hom (K.pOpcycles j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (ShortComplex.mk (K.d i j) (K.pOpcycles j) (K.d_pOpcycles i j))).1
    (ShortComplex.exact_of_g_is_cokernel _ (K.opcyclesIsCokernel i j hij))

/-- The sequence `Hᵢ → Kᵢ / Bᵢ → Zⱼ`, whose second map is induced by the differential `dᵢⱼ`, is
exact. -/
lemma moduleCat_exact_homologyι_opcyclesToCycles {i j : ι} (hij : c.Rel i j) :
    Function.Exact (K.homologyι i).hom (K.opcyclesToCycles i j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j)
      (K.homologyι_opcyclesToCycles i j))).1
    ((HomologySequence.composableArrows₃_exact K i j hij).exact 0)

/-- The sequence `Kᵢ / Bᵢ → Zⱼ → Hⱼ`, whose first map is induced by the differential `dᵢⱼ`, is
exact. -/
lemma moduleCat_exact_opcyclesToCycles_homologyπ {i j : ι} (hij : c.Rel i j) :
    Function.Exact (K.opcyclesToCycles i j).hom (K.homologyπ j).hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
    (ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j)
      (K.opcyclesToCycles_homologyπ i j))).1
    ((HomologySequence.composableArrows₃_exact K i j hij).exact 1)

/-- The class in the opcycles of a cycle is the image of its homology class, on elements. -/
@[simp]
lemma moduleCat_homologyι_homologyπ_apply (i : ι) (z : K.cycles i) :
    (K.homologyι i).hom ((K.homologyπ i).hom z) = (K.pOpcycles i).hom ((K.iCycles i).hom z) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (K.homology_π_ι i)) z

/-- The map `Kᵢ / Bᵢ → Zⱼ` induced by the differential sends the class of `x` to the cycle
`dᵢⱼ x`, on elements. -/
@[simp]
lemma moduleCat_opcyclesToCycles_pOpcycles_apply (i j : ι) (x : K.X i) :
    (K.opcyclesToCycles i j).hom ((K.pOpcycles i).hom x) = (K.toCycles i j).hom x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (K.pOpcycles_opcyclesToCycles i j)) x

/-- Over a Noetherian ring, the cycles of a finitely generated term of a complex are finitely
generated. -/
instance moduleFinite_cycles [IsNoetherianRing R] (i : ι) [Module.Finite R (K.X i)] :
    Module.Finite R (K.cycles i) :=
  .of_injective (K.iCycles i).hom (K.moduleCat_iCycles_injective i)

/-- The opcycles of a finitely generated term of a complex are finitely generated. -/
instance moduleFinite_opcycles (i : ι) [Module.Finite R (K.X i)] :
    Module.Finite R (K.opcycles i) :=
  .of_surjective (K.pOpcycles i).hom (K.moduleCat_pOpcycles_surjective i)

/-- The homology of a complex is finitely generated where its cycles are. -/
instance moduleFinite_homology (i : ι) [Module.Finite R (K.cycles i)] :
    Module.Finite R (K.homology i) :=
  .of_surjective (K.homologyπ i).hom (K.moduleCat_homologyπ_surjective i)

end HomologicalComplex
