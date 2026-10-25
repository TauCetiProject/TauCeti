/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ConcreteCategory

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
A linear map into `K.X n` whose values are cycles induces a class map into the homology,
`HomologicalComplex.moduleCatHomologyClass`; it is surjective when every cycle is a value, its
kernel consists of the elements sent to boundaries, and chain maps act on it compatibly.
Consequently, when `K` is the union of subcomplexes `L i`, every homology class of `K` comes from
some `L i` (`HomologicalComplex.exists_homologyMap_eq_of_injective`).  Two cycles whose difference
is a boundary have the same homology class
(`HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d`), and a cycle has zero homology
class exactly when it is a boundary (`HomologicalComplex.moduleCat_homologyπ_eq_zero_iff`).
Given concrete cocycle and coboundary submodules identified with the terms of a cochain complex,
`HomologicalComplex.moduleCatCohomologyClassOfIso` specializes this class map to the cocycles,
with its surjectivity and its kernel described by the coboundaries.  When the differential is a
linear map `δ` under these identifications, the kernels of `δ` and the coboundaries `0, im δ, …`
satisfy the hypotheses of this construction (`HomologicalComplex.moduleCat_d_inv_eq_zero_iff`,
`HomologicalComplex.moduleCat_mem_iff_exists_d_eq_inv`).  At a degree where the complex
is exact, the image of the incoming differential, the term and the image of the outgoing
differential form a short exact sequence (`HomologicalComplex.exact_subtype_rangeRestrict`).
A chain map restricts to a map between the images of the differentials
(`HomologicalComplex.Hom.boundaryMap`), functorially in the chain map
(`HomologicalComplex.Hom.boundaryMap_comp`), and injective where the chain map is; for a
degreewise short exact sequence of complexes whose third term is exact, these maps form a sequence
exact in the middle (`HomologicalComplex.Hom.exact_boundaryMap`).
-/

public section

open CategoryTheory

namespace HomologicalComplex

/-- A chain map of complexes of modules commutes with the differentials, on elements. -/
theorem Hom.comm_apply {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L) (i j : ι) (x : K.X i) :
    L.d i j (φ.f i x) = φ.f j (K.d i j x) := by
  rw [← ModuleCat.comp_apply, φ.comm, ModuleCat.comp_apply]

/-- A chain map of complexes of modules sends cycles to cycles, on elements. -/
theorem Hom.d_apply_eq_zero_of_d_apply_eq_zero {R : Type*} [Ring R] {ι : Type*}
    {c : ComplexShape ι} {K L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L) (i j : ι)
    (x : K.X i) (hx : (K.d i j).hom x = 0) : (L.d i j).hom ((φ.f i).hom x) = 0 :=
  (Hom.comm_apply φ i j x).trans ((congrArg _ hx).trans (map_zero _))

/-- In a complex of modules the differential of a differential vanishes, on elements. -/
theorem d_comp_d_apply {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat R) c) (i j l : ι) (x : K.X i) :
    K.d j l (K.d i j x) = 0 := by
  rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
  rfl

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) (n : ι)

variable {K} in
/-- At a degree `j` where a complex of modules is exact, the inclusion of the image of the incoming
differential `K.X i ⟶ K.X j` and the corestriction of the outgoing differential `K.X j ⟶ K.X k` to
its image form a short exact sequence. -/
theorem exact_subtype_rangeRestrict {i j k : ι} (hi : c.prev j = i) (hk : c.next j = k)
    (h : K.ExactAt j) :
    Function.Exact (LinearMap.range (K.d i j).hom).subtype (K.d j k).hom.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).1
    ((K.exactAt_iff' i j k hi hk).1 h)).symm

section BoundaryMap

variable {K L M : HomologicalComplex (ModuleCat R) c}

/-- A chain map of complexes of modules sends the image of the differential `K.X i ⟶ K.X j` into
the image of the differential `L.X i ⟶ L.X j`. -/
def Hom.boundaryMap (φ : K ⟶ L) (i j : ι) :
    LinearMap.range (K.d i j).hom →ₗ[R] LinearMap.range (L.d i j).hom :=
  (φ.f j).hom.restrict fun _ ⟨y, hy⟩ ↦ ⟨(φ.f i).hom y, by rw [Hom.comm_apply, hy]⟩

/-- The map on boundaries induced by a chain map is the restriction of the chain map. -/
@[simp]
theorem Hom.coe_boundaryMap (φ : K ⟶ L) (i j : ι) (x : LinearMap.range (K.d i j).hom) :
    (φ.boundaryMap i j x : L.X j) = (φ.f j).hom x :=
  (rfl)

/-- The identity chain map induces the identity on boundaries. -/
@[simp]
theorem Hom.boundaryMap_id (i j : ι) : (𝟙 K : K ⟶ K).boundaryMap i j = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

/-- The map on boundaries induced by a composite of chain maps is the composite of the induced
maps. -/
@[simp]
theorem Hom.boundaryMap_comp (φ : K ⟶ L) (ψ : L ⟶ M) (i j : ι) :
    (φ ≫ ψ).boundaryMap i j = ψ.boundaryMap i j ∘ₗ φ.boundaryMap i j :=
  LinearMap.ext fun _ ↦ Subtype.ext rfl

/-- A chain map that is injective in degree `j` is injective on the boundaries of degree `j`. -/
theorem Hom.boundaryMap_injective (φ : K ⟶ L) (i : ι) {j : ι}
    (hφ : Function.Injective (φ.f j).hom) : Function.Injective (φ.boundaryMap i j) :=
  fun _ _ hxy ↦ Subtype.ext (hφ (congrArg Subtype.val hxy))

/-- Let `K ⟶ L ⟶ M` be chain maps of complexes of modules, let `h = c.prev i` and
`j = c.next i`. If the sequence `K ⟶ L ⟶ M` is exact in degrees `i` and `j`, `L ⟶ M` is
surjective in degree `h` and `M` is exact in degree `i`, then the induced maps on the images of
the differentials `K.X i ⟶ K.X j`, `L.X i ⟶ L.X j` and `M.X i ⟶ M.X j` form a sequence that is
exact in the middle. -/
theorem Hom.exact_boundaryMap {φ : K ⟶ L} {ψ : L ⟶ M} {h i j : ι} (hh : c.prev i = h)
    (hj : c.next i = j) (hi : Function.Exact (φ.f i).hom (ψ.f i).hom)
    (hj' : Function.Exact (φ.f j).hom (ψ.f j).hom) (hψ : Function.Surjective (ψ.f h).hom)
    (hM : M.ExactAt i) : Function.Exact (φ.boundaryMap i j) (ψ.boundaryMap i j) := by
  rintro ⟨_, x, rfl⟩
  constructor
  · intro hx
    have hx' : (M.d i j).hom ((ψ.f i).hom x) = 0 := by
      rw [Hom.comm_apply]
      exact congrArg Subtype.val hx
    -- The image of `x` in `M.X i` is a cycle, hence the boundary of some `ψ w`; then
    -- `x - d w` comes from `K.X i` and has the same boundary as `x`.
    obtain ⟨⟨_, z, rfl⟩, hz⟩ := ((exact_subtype_rangeRestrict hh hj hM) _).1 (Subtype.ext hx')
    obtain ⟨w, rfl⟩ := hψ z
    obtain ⟨x', hx''⟩ := (hi (x - (L.d h i).hom w)).1 (by
      rw [map_sub, ← Hom.comm_apply, sub_eq_zero]
      exact hz.symm)
    refine ⟨⟨(K.d i j).hom x', x', rfl⟩, Subtype.ext ?_⟩
    rw [coe_boundaryMap, ← Hom.comm_apply, hx'', map_sub, d_comp_d_apply, sub_zero]
  · rintro ⟨x', hx'⟩
    rw [← hx']
    exact Subtype.ext (hj'.apply_apply_eq_zero _)

end BoundaryMap

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

section HomologyClass

variable {n} {m : ι} (hm : c.next n = m) {Z : Type*} [AddCommGroup Z] [Module R Z]
  (j : Z →ₗ[R] K.X n) (hj : ∀ z, K.d n m (j z) = 0)

/-- The homology class map of a linear map `j` into the degree-`n` term of a complex of modules
whose values are cycles. The source of `j` need not be a submodule of a module identified with the
term, so subcomplexes are covered. -/
noncomputable def moduleCatHomologyClass : Z →ₗ[R] K.homology n :=
  (K.homologyπ n).hom ∘ₗ (K.sc n).moduleCatCyclesIso.inv.hom ∘ₗ
    j.codRestrict _ fun z ↦ by subst hm; exact hj z

/-- The class of `z` is the homology class of the cycle `j z`. -/
lemma moduleCatHomologyClass_apply (z : Z) :
    K.moduleCatHomologyClass hm j hj z =
      K.homologyπ n (K.moduleCatCyclesMk (j z) m hm (hj z)) :=
  (rfl)

/-- If every degree-`n` cycle is a value of `j`, then every homology class is the class of an
element. -/
lemma moduleCatHomologyClass_surjective (h : ∀ x : K.X n, K.d n m x = 0 → ∃ z, j z = x) :
    Function.Surjective (K.moduleCatHomologyClass hm j hj) := by
  intro x
  obtain ⟨y, rfl⟩ := K.moduleCat_homologyπ_surjective n x
  obtain ⟨z, hz⟩ := h (K.iCycles n y) <| by
    subst hm
    rw [← ConcreteCategory.comp_apply, K.iCycles_d]
    rfl
  refine ⟨z, ?_⟩
  rw [moduleCatHomologyClass_apply]
  congr 1
  apply K.moduleCat_iCycles_injective n
  rw [iCycles_moduleCatCyclesMk, hz]

/-- The class of `z` vanishes exactly when `j z` is a boundary, the image of an element of the
term of degree `c.prev n`. -/
lemma moduleCatHomologyClass_eq_zero_iff {p : ι} (hp : c.prev n = p) (z : Z) :
    K.moduleCatHomologyClass hm j hj z = 0 ↔ ∃ y : K.X p, K.d p n y = j z := by
  rw [moduleCatHomologyClass_apply, K.moduleCat_homologyπ_eq_zero_iff hp]
  refine exists_congr fun y ↦ ?_
  rw [← (K.moduleCat_iCycles_injective n).eq_iff, iCycles_moduleCatCyclesMk,
    ← ModuleCat.comp_apply, toCycles_i]

variable {K} in
/-- A chain map `φ` sends the class of `z` to the class of `g z` when it carries `j z` to
`j' (g z)`. -/
lemma homologyMap_moduleCatHomologyClass {L : HomologicalComplex (ModuleCat R) c} (φ : K ⟶ L)
    {Z' : Type*} [AddCommGroup Z'] [Module R Z'] (j' : Z' →ₗ[R] L.X n)
    (hj' : ∀ z, L.d n m (j' z) = 0) (g : Z →ₗ[R] Z') (h : ∀ z, φ.f n (j z) = j' (g z)) (z : Z) :
    homologyMap φ n (K.moduleCatHomologyClass hm j hj z) =
      L.moduleCatHomologyClass hm j' hj' (g z) := by
  rw [moduleCatHomologyClass_apply, moduleCatHomologyClass_apply, ← ModuleCat.comp_apply,
    homologyπ_naturality, ModuleCat.comp_apply]
  congr 1
  apply L.moduleCat_iCycles_injective n
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, iCycles_moduleCatCyclesMk,
    iCycles_moduleCatCyclesMk, h]

end HomologyClass

section CochainPresentation

variable (K : CochainComplex (ModuleCat R) ℕ)
variable (V : ℕ → Type*) [∀ n, AddCommGroup (V n)] [∀ n, Module R (V n)]
variable (Z B : ∀ n, Submodule R (V n))
variable (e : ∀ n, K.X n ≅ ModuleCat.of R (V n))
variable (hZ : ∀ (n : ℕ) (z : V n),
  z ∈ Z n ↔ K.d n (n + 1) ((e n).inv z) = 0)
variable (hB : ∀ (n : ℕ) (z : V n),
  z ∈ B n ↔ ∃ y : K.X ((ComplexShape.up ℕ).prev n),
    K.d ((ComplexShape.up ℕ).prev n) n y = (e n).inv z)

section Differential

variable {V e} (δ : ∀ n, V n →ₗ[R] V (n + 1))
  (hδ : ∀ n, K.d n (n + 1) ≫ (e (n + 1)).hom = (e n).hom ≫ ModuleCat.ofHom (δ n))
include hδ

/-- If the differential is `δ` under the identifications `e` of the terms, then an element of
`V n` is killed by `δ n` exactly when the differential kills its transport into the complex. -/
lemma moduleCat_d_inv_eq_zero_iff {n : ℕ} (z : V n) :
    K.d n (n + 1) ((e n).inv z) = 0 ↔ δ n z = 0 := by
  have h := ConcreteCategory.congr_hom (hδ n) ((e n).inv z)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, Iso.inv_hom_id_apply, ModuleCat.ofHom_apply] at h
  rw [← h]
  exact ⟨fun h0 ↦ by rw [h0, map_zero], fun h0 ↦ by
    rw [← Iso.hom_inv_id_apply (e (n + 1)) (K.d n (n + 1) _), h0, map_zero]⟩

/-- If the differential is `δ` under the identifications `e` of the terms, and `B` consists of
`0` in degree zero and of the image of `δ n` in degree `n + 1`, then `B` consists exactly of the
elements whose transport into the complex is in the image of the incoming differential. -/
lemma moduleCat_mem_iff_exists_d_eq_inv (hB₀ : B 0 = ⊥)
    (hB_succ : ∀ n, B (n + 1) = LinearMap.range (δ n)) (n : ℕ) (z : V n) :
    z ∈ B n ↔ ∃ y : K.X ((ComplexShape.up ℕ).prev n),
      K.d ((ComplexShape.up ℕ).prev n) n y = (e n).inv z := by
  cases n with
  | zero =>
    rw [hB₀, Submodule.mem_bot, CochainComplex.prev_nat_zero, K.shape 0 0 (by simp)]
    refine ⟨fun hz ↦ ⟨0, by rw [hz, map_zero, map_zero]⟩, fun ⟨y, hy⟩ ↦ ?_⟩
    rw [← Iso.inv_hom_id_apply (e 0) z, ← hy]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
  | succ n =>
    have h (y : K.X n) : (e (n + 1)).hom (K.d n (n + 1) y) = δ n ((e n).hom y) := by
      rw [← ModuleCat.comp_apply, hδ n, ModuleCat.comp_apply, ModuleCat.ofHom_apply]
    rw [hB_succ, LinearMap.mem_range, CochainComplex.prev_nat_succ]
    constructor
    · rintro ⟨ψ, rfl⟩
      refine ⟨(e n).inv ψ, ?_⟩
      rw [← Iso.hom_inv_id_apply (e (n + 1)) (K.d n (n + 1) _), h, Iso.inv_hom_id_apply]
    · rintro ⟨y, hy⟩
      exact ⟨(e n).hom y, by rw [← h, hy, Iso.inv_hom_id_apply]⟩

end Differential

/-- The linear map sending a cocycle of a cochain complex of modules to its cohomology class, the
homology class map of the cocycles transported through the chosen identifications of the terms. -/
noncomputable def moduleCatCohomologyClassOfIso (n : ℕ) : Z n →ₗ[R] K.homology n :=
  K.moduleCatHomologyClass (CochainComplex.next ℕ n) ((e n).inv.hom ∘ₗ (Z n).subtype)
    fun z ↦ (hZ n z.1).1 z.2

/-- The class of a cocycle is the homology class of the cocycle transported into the complex. -/
lemma moduleCatCohomologyClassOfIso_apply (n : ℕ) (z : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z =
      K.homologyπ n (K.moduleCatCyclesMk ((e n).inv z.1) (n + 1) (CochainComplex.next ℕ n)
        ((hZ n z.1).1 z.2)) :=
  (rfl)

/-- The class of a cocycle `z` is the homology class of any cycle whose underlying element
corresponds to `z` under the identification of the term. -/
lemma moduleCatCohomologyClassOfIso_eq_homologyπ {n : ℕ} (z : Z n) (y : K.cycles n)
    (hy : (e n).hom (K.iCycles n y) = z.1) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z = K.homologyπ n y := by
  rw [moduleCatCohomologyClassOfIso_apply]
  congr 1
  apply K.moduleCat_iCycles_injective n
  rw [iCycles_moduleCatCyclesMk, ← hy, Iso.hom_inv_id_apply]

/-- Every cohomology class of a cochain complex of modules is represented by a cocycle. -/
lemma moduleCatCohomologyClassOfIso_surjective (n : ℕ) :
    Function.Surjective (K.moduleCatCohomologyClassOfIso V Z e hZ n) :=
  K.moduleCatHomologyClass_surjective _ _ _ fun x hx ↦
    ⟨⟨(e n).hom x, (hZ n _).2 (by rwa [Iso.hom_inv_id_apply])⟩, Iso.hom_inv_id_apply (e n) x⟩

/-- A cocycle has zero class exactly when its underlying element is in the image of the incoming
differential from the degree preceding it. -/
lemma moduleCatCohomologyClassOfIso_eq_zero_iff_exists {n m : ℕ}
    (hm : (ComplexShape.up ℕ).prev n = m) (z : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z = 0 ↔
      ∃ y, K.d m n y = (e n).inv z.1 :=
  K.moduleCatHomologyClass_eq_zero_iff _ _ _ hm z

include hB

/-- The class of a cocycle is zero exactly when its underlying element is a coboundary. -/
lemma moduleCatCohomologyClassOfIso_eq_zero_iff (n : ℕ) (z : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z = 0 ↔ z.1 ∈ B n := by
  rw [K.moduleCatCohomologyClassOfIso_eq_zero_iff_exists V Z e hZ rfl]
  exact (hB n z.1).symm

/-- Two cocycles represent the same cohomology class exactly when their difference is a
coboundary. -/
lemma moduleCatCohomologyClassOfIso_eq_iff (n : ℕ) (z w : Z n) :
    K.moduleCatCohomologyClassOfIso V Z e hZ n z =
        K.moduleCatCohomologyClassOfIso V Z e hZ n w ↔ (z - w).1 ∈ B n := by
  rw [← sub_eq_zero, ← map_sub, moduleCatCohomologyClassOfIso_eq_zero_iff K V Z B e hZ hB]

end CochainPresentation

variable {n} in
/-- Every degree-`n` homology class of a complex of modules is the class of an element killed by
the differential out of degree `n`. -/
lemma exists_homologyπ_moduleCatCyclesMk_eq (m : ι) (hm : c.next n = m) (z : K.homology n) :
    ∃ (x : K.X n) (hx : K.d n m x = 0), K.homologyπ n (K.moduleCatCyclesMk x m hm hx) = z := by
  obtain ⟨z, rfl⟩ := K.moduleCat_homologyπ_surjective n z
  have hz : K.d n m (K.iCycles n z) = 0 := by
    rw [← ModuleCat.comp_apply, iCycles_d]
    rfl
  exact ⟨_, hz,
    congrArg _ (K.moduleCat_iCycles_injective n (iCycles_moduleCatCyclesMk _ _ _ _ _ _))⟩

variable {n} in
/-- A finite sum of cycles built by `moduleCatCyclesMk` is the cycle built from the sum. -/
lemma sum_moduleCatCyclesMk {κ : Type*} (s : Finset κ) (x : κ → K.X n) (m : ι)
    (hm : c.next n = m) (hx : ∀ i, K.d n m (x i) = 0) :
    ∑ i ∈ s, K.moduleCatCyclesMk (x i) m hm (hx i) =
      K.moduleCatCyclesMk (∑ i ∈ s, x i) m hm
        (by rw [map_sum]; exact Finset.sum_eq_zero fun i _ ↦ hx i) :=
  K.moduleCat_iCycles_injective n (by simp only [map_sum, iCycles_moduleCatCyclesMk])

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

variable {K} in
/-- A chain map of complexes of modules sends the class of a cycle to the class of its image. -/
lemma homologyMap_homologyπ_moduleCatCyclesMk {L : HomologicalComplex (ModuleCat R) c}
    (φ : K ⟶ L) {n : ι} (x : K.X n) (m : ι) (hm : c.next n = m) (hx : K.d n m x = 0) :
    (homologyMap φ n).hom ((K.homologyπ n).hom (K.moduleCatCyclesMk x m hm hx)) =
      (L.homologyπ n).hom (L.moduleCatCyclesMk ((φ.f n).hom x) m hm
        (by rw [Hom.comm_apply, hx, map_zero])) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, homologyπ_naturality, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  congr 1
  apply L.moduleCat_iCycles_injective
  rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, iCycles_moduleCatCyclesMk,
    iCycles_moduleCatCyclesMk]

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex (ModuleCat R) c)} (hS : S.ShortExact)

/-- **The connecting map of a short exact sequence of complexes of modules, on classes.** Let `z₃`
be a cycle of `S.X₃` in degree `i`, `x₂` an element of `S.X₂` in degree `i` lifting it, and `z₁` a
cycle of `S.X₁` in degree `j` whose image in `S.X₂` is the differential of `x₂`.  Then the
connecting map sends the class of `z₃` to the class of `z₁`. -/
theorem moduleCat_δ_homologyπ (i j : ι) (hij : c.Rel i j) (z₃ : S.X₃.cycles i) (x₂ : S.X₂.X i)
    (hx₂ : (S.g.f i).hom x₂ = (S.X₃.iCycles i).hom z₃) (z₁ : S.X₁.cycles j)
    (hz₁ : (S.f.f j).hom ((S.X₁.iCycles j).hom z₁) = (S.X₂.d i j).hom x₂) :
    (hS.δ i j hij).hom ((S.X₃.homologyπ i).hom z₃) = (S.X₁.homologyπ j).hom z₁ := by
  have hd₃ : (S.X₃.d i j).hom ((S.X₃.iCycles i).hom z₃) = 0 := by
    rw [← ModuleCat.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  -- Mathlib's computation of the connecting map, for the cycle `iCycles z₃` and the lift `x₂`.
  have key := hS.δ_apply i j hij ((S.X₃.iCycles i).hom z₃) hd₃ x₂ hx₂
    ((S.X₁.iCycles j).hom z₁) hz₁ (c.next j) rfl
  -- The cycles built by `cyclesMk` from `iCycles z₃` and `iCycles z₁` are `z₃` and `z₁`.
  have h₃ : S.X₃.cyclesMk ((S.X₃.iCycles i).hom z₃) j (c.next_eq' hij) hd₃ = z₃ :=
    S.X₃.moduleCat_iCycles_injective i
      (HomologicalComplex.i_cyclesMk (C := ModuleCat R) S.X₃ _ j (c.next_eq' hij) hd₃)
  have h₁ : S.X₁.cyclesMk ((S.X₁.iCycles j).hom z₁) (c.next j) rfl
      (hS.d_eq_zero_of_f_eq_d_apply i j x₂ _ hz₁ _) = z₁ :=
    S.X₁.moduleCat_iCycles_injective j
      (HomologicalComplex.i_cyclesMk (C := ModuleCat R) S.X₁ _ (c.next j) rfl _)
  rw [h₃, h₁] at key
  exact key

end CategoryTheory.ShortComplex.ShortExact
