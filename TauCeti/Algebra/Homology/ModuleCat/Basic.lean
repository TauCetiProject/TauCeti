/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Cycles and homology of homological complexes of modules

For a homological complex `K` of modules over a ring, the inclusion of the degree-`n` cycles into
`K.X n` is injective and the class map from the cycles onto the degree-`n` homology is surjective.
These are the elementwise forms of the facts that `K.iCycles n` is a monomorphism and
`K.homologyπ n` is an epimorphism.  Chain maps commute with the differentials and the square of
the differential vanishes, on elements (`HomologicalComplex.Hom.comm_apply`,
`HomologicalComplex.d_comp_d_apply`).  Conversely, an element of `K.X n` killed by the differential
is a cycle, `HomologicalComplex.moduleCatCyclesMk`.  This constructor directly returns
an element of `K.cycles n` for modules over a ring in any universe, whereas Mathlib's
`HomologicalComplex.cyclesMk` returns an element of `(forget₂ C Ab).obj (K.cycles n)`.
Consequently, when `K` is the union of subcomplexes `L i`, every homology class of `K` comes from
some `L i` (`HomologicalComplex.exists_homologyMap_eq_of_injective`).  Two cycles whose difference
is a boundary have the same homology class
(`HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d`), and a cycle has zero homology
class exactly when it is a boundary (`HomologicalComplex.moduleCat_homologyπ_eq_zero_iff`).

For a cochain complex `K` of modules indexed by `ℕ` whose terms are identified with modules `V n`,
under which the differential becomes a linear map `d n : V n →ₗ V (n + 1)`, the class map
`CochainComplex.moduleCatCocycleClass` sends an element of the kernel of `d n` to its cohomology
class. It is surjective, injective in degree zero, and in degree `n + 1` its kernel is the image of
`d n`. This describes the cohomology concretely as cocycles modulo coboundaries.
-/

public section

open CategoryTheory

namespace HomologicalComplex

/-- A chain map of complexes of modules commutes with the differentials, on elements. -/
theorem Hom.comm_apply {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L) (i j : ι) (x : K.X i) :
    L.d i j (φ.f i x) = φ.f j (K.d i j x) := by
  rw [← ModuleCat.comp_apply, φ.comm, ModuleCat.comp_apply]

/-- In a complex of modules the differential of a differential vanishes, on elements. -/
theorem d_comp_d_apply {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (i j l : ι) (x : K.X i) :
    K.d j l (K.d i j x) = 0 := by
  rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
  rfl

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) (n : ι)

/-- The inclusion of the degree-`n` cycles of a homological complex of modules into its degree-`n`
term is injective. -/
lemma moduleCat_iCycles_injective : Function.Injective (K.iCycles n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The class map from the degree-`n` cycles of a homological complex of modules onto its
degree-`n` homology is surjective. -/
lemma moduleCat_homologyπ_surjective : Function.Surjective (K.homologyπ n) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

variable {n} in
/-- A degree-`n` cycle of a homological complex of modules has zero homology class exactly when it
is a boundary, the image of an element of the term of degree `c.prev n`. -/
lemma moduleCat_homologyπ_eq_zero_iff {m : ι} (hm : c.prev n = m) (z : K.cycles n) :
    K.homologyπ n z = 0 ↔ ∃ y : K.X m, K.toCycles m n y = z := by
  refine ⟨(ShortComplex.moduleCat_exact_iff _).1 (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (K.toCycles m n) (K.homologyπ n) (K.toCycles_comp_homologyπ m n))
    (K.homologyIsCokernel m n hm)) z, ?_⟩
  rintro ⟨y, rfl⟩
  rw [← ModuleCat.comp_apply, toCycles_comp_homologyπ]
  rfl

variable {n} in
/-- An element `x` of `K.X n` killed by the differential `K.d n m` out of degree `n`, as a cycle
of degree `n`. -/
noncomputable def moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨x, by subst hm; exact hx⟩

/-- The cycle `K.moduleCatCyclesMk x m hm hx` has underlying element `x`. -/
@[simp]
lemma iCycles_moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.iCycles n (K.moduleCatCyclesMk x m hm hx) = x :=
  (K.sc n).moduleCatCyclesIso_inv_iCycles_apply _

variable {n} in
/-- Two degree-`n` cycles of a complex of modules whose difference is a boundary have the same
homology class. -/
lemma moduleCat_homologyπ_eq_of_iCycles_sub_eq_d {z w : K.cycles n} {m : ι} (b : K.X m)
    (h : K.iCycles n z - K.iCycles n w = K.d m n b) : K.homologyπ n z = K.homologyπ n w := by
  have hb : z - w = K.toCycles m n b := K.moduleCat_iCycles_injective n <| by
    rw [map_sub, h, ← ModuleCat.comp_apply, toCycles_i]
  rw [← sub_eq_zero, ← map_sub, hb, ← ModuleCat.comp_apply, toCycles_comp_homologyπ]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply]

variable {K} in
/-- **Homology classes of a union of subcomplexes.** Let `φ i : L i ⟶ K` be chain maps of
complexes of modules that are injective in degree `c.next n`, and suppose every element of `K.X n`
comes from some `L i`. Then every degree-`n` homology class of `K` comes from some `L i`. -/
theorem exists_homologyMap_eq_of_injective {κ : Type*}
    {L : κ → HomologicalComplex (ModuleCat R) c} (φ : ∀ i, L i ⟶ K)
    (hφ : ∀ i, Function.Injective ((φ i).f (c.next n)))
    (h : ∀ x : K.X n, ∃ i y, (φ i).f n y = x) (z : K.homology n) :
    ∃ i y, homologyMap (φ i) n y = z := by
  obtain ⟨z, rfl⟩ := K.moduleCat_homologyπ_surjective n z
  obtain ⟨i, y, hy⟩ := h (K.iCycles n z)
  -- the lift `y` of the cycle is again a cycle, since its differential maps to zero injectively
  have hdy : (L i).d n (c.next n) y = 0 := hφ i <| by
    rw [← Hom.comm_apply, hy, map_zero, ← ModuleCat.comp_apply, K.iCycles_d]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply]
  refine ⟨i, (L i).homologyπ n ((L i).moduleCatCyclesMk y _ rfl hdy), ?_⟩
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply K.moduleCat_iCycles_injective
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, iCycles_moduleCatCyclesMk, hy]

end HomologicalComplex

namespace CochainComplex

universe v

variable {R : Type*} [Ring R] (K : CochainComplex (ModuleCat.{v} R) ℕ) {V : ℕ → Type v}
  [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)] (e : ∀ n, K.X n ≅ ModuleCat.of R (V n))
  (d : ∀ n, V n →ₗ[R] V (n + 1))
  (hd : ∀ n, K.d n (n + 1) ≫ (e (n + 1)).hom = (e n).hom ≫ ModuleCat.ofHom (d n))

include hd in
/-- Under the identifications `e`, the differential of `K` is `d`, on elements. -/
private lemma hom_d_apply (n : ℕ) (x : K.X n) :
    (e (n + 1)).hom (K.d n (n + 1) x) = d n ((e n).hom x) := by
  rw [← ModuleCat.comp_apply, hd, ModuleCat.comp_apply, ModuleCat.ofHom_apply]

include hd in
/-- An element of the kernel of `d n` corresponds to an element of `K.X n` killed by the
differential. -/
private lemma d_inv_apply_eq_zero {n : ℕ} {x : V n} (hx : x ∈ LinearMap.ker (d n)) :
    K.d n (n + 1) ((e n).inv x) = 0 := by
  apply (ModuleCat.mono_iff_injective (e (n + 1)).hom).1 inferInstance
  rw [hom_d_apply K e d hd, Iso.inv_hom_id_apply, map_zero]
  exact LinearMap.mem_ker.1 hx

include hd in
/-- The element of `V n` underlying a degree-`n` cycle of `K` lies in the kernel of `d n`. -/
theorem hom_iCycles_mem_ker {n : ℕ} (z : K.cycles n) :
    (e n).hom (K.iCycles n z) ∈ LinearMap.ker (d n) := by
  rw [LinearMap.mem_ker, ← hom_d_apply K e d hd, ← ModuleCat.comp_apply (K.iCycles n), K.iCycles_d]
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]

include hd in
/-- Every element of the kernel of `d n` underlies a degree-`n` cycle of `K`. -/
theorem exists_hom_iCycles_eq_of_mem_ker {n : ℕ} {x : V n} (hx : x ∈ LinearMap.ker (d n)) :
    ∃ z : K.cycles n, (e n).hom (K.iCycles n z) = x :=
  ⟨K.moduleCatCyclesMk ((e n).inv x) (n + 1) (by simp) (d_inv_apply_eq_zero K e d hd hx), by
    rw [HomologicalComplex.iCycles_moduleCatCyclesMk, Iso.inv_hom_id_apply]⟩

/-- The cohomology class of an element of the kernel of `d n`, a degree-`n` cocycle under the
identifications `e` of the terms of `K` with the modules `V n`. -/
noncomputable def moduleCatCocycleClass (n : ℕ) : LinearMap.ker (d n) →ₗ[R] K.homology n :=
  (K.liftCycles (ModuleCat.ofHom (LinearMap.ker (d n)).subtype ≫ (e n).inv) (n + 1) (by simp)
    (ModuleCat.hom_ext (LinearMap.ext fun x ↦ by
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.hom_ofHom, Submodule.subtype_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
      exact d_inv_apply_eq_zero K e d hd x.2)) ≫ K.homologyπ n).hom

/-- The class of a cocycle `x` is the homology class of any cycle of `K` whose underlying element
is `x`. -/
theorem moduleCatCocycleClass_eq_homologyπ {n : ℕ} (x : LinearMap.ker (d n)) (z : K.cycles n)
    (hz : (e n).hom (K.iCycles n z) = x) :
    K.moduleCatCocycleClass e d hd n x = K.homologyπ n z := by
  rw [moduleCatCocycleClass, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  apply K.moduleCat_iCycles_injective n
  rw [← ModuleCat.comp_apply _ (K.iCycles n), HomologicalComplex.liftCycles_i, ModuleCat.comp_apply,
    ModuleCat.ofHom_apply, Submodule.subtype_apply, ← hz, Iso.hom_inv_id_apply]

/-- Every degree-`n` cohomology class of `K` is the class of a cocycle. -/
theorem moduleCatCocycleClass_surjective (n : ℕ) :
    Function.Surjective (K.moduleCatCocycleClass e d hd n) := by
  intro c
  obtain ⟨z, rfl⟩ := K.moduleCat_homologyπ_surjective n c
  exact ⟨⟨_, K.hom_iCycles_mem_ker e d hd z⟩, K.moduleCatCocycleClass_eq_homologyπ e d hd _ z rfl⟩

/-- In degree zero the class map is injective: there are no nonzero coboundaries. -/
theorem moduleCatCocycleClass_zero_injective :
    Function.Injective (K.moduleCatCocycleClass e d hd 0) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨z, hz⟩ := K.exists_hom_iCycles_eq_of_mem_ker e d hd x.2
  rw [K.moduleCatCocycleClass_eq_homologyπ e d hd x z hz,
    K.moduleCat_homologyπ_eq_zero_iff prev_nat_zero] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← ModuleCat.comp_apply (K.toCycles 0 0), HomologicalComplex.toCycles_i, K.shape 0 0 (by simp)]
    at hz
  simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] at hz
  exact Subtype.ext hz.symm

/-- In degree `n + 1` a cocycle has zero class exactly when it is a coboundary, an element of the
image of `d n`. -/
theorem moduleCatCocycleClass_succ_eq_zero_iff {n : ℕ} (x : LinearMap.ker (d (n + 1))) :
    K.moduleCatCocycleClass e d hd (n + 1) x = 0 ↔ (x : V (n + 1)) ∈ LinearMap.range (d n) := by
  obtain ⟨z, hz⟩ := K.exists_hom_iCycles_eq_of_mem_ker e d hd x.2
  rw [K.moduleCatCocycleClass_eq_homologyπ e d hd x z hz,
    K.moduleCat_homologyπ_eq_zero_iff (prev_nat_succ n), LinearMap.mem_range, ← hz]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(e n).hom y, ?_⟩
    rw [← hom_d_apply K e d hd, ← ModuleCat.comp_apply (K.toCycles n (n + 1)),
      HomologicalComplex.toCycles_i]
  · rintro ⟨w, hw⟩
    refine ⟨(e n).inv w, K.moduleCat_iCycles_injective _ ?_⟩
    apply (ModuleCat.mono_iff_injective (e (n + 1)).hom).1 inferInstance
    rw [← hw, ← ModuleCat.comp_apply (K.toCycles n (n + 1)), HomologicalComplex.toCycles_i,
      hom_d_apply K e d hd, Iso.inv_hom_id_apply]

end CochainComplex
