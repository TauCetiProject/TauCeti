/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra
public import TauCeti.Algebra.Lie.Cohomology.ChevalleyEilenberg

/-!
# Relative Lie algebra cohomology

Let `L` be a Lie algebra over a commutative ring `R`, `𝔨` a Lie subalgebra and `M` an `L`-module.
The cochains of `L` relative to `𝔨` are the Chevalley–Eilenberg cochains `ω` which vanish as soon
as one argument lies in `𝔨` (`ι_x ω = 0` for `x ∈ 𝔨`) and which are invariant under `𝔨`
(`⁅x, ω⁆ = 0` for `x ∈ 𝔨`). Equivalently, they are the `𝔨`-equivariant alternating maps
`⋀ⁿ (L ⧸ 𝔨) → M`, so that `C^n(L, 𝔨; M) = Hom_𝔨(⋀ⁿ (L ⧸ 𝔨), M)`. By Cartan's formula
`ι_x d ω = ⁅x, ω⁆ - d ι_x ω` and since `d` commutes with the action of `L`, the differential
preserves these two conditions, so the relative cochains form a subcomplex of the
Chevalley–Eilenberg complex. Its cohomology is the relative Lie algebra cohomology
`H^n(L, 𝔨; M)`.

For a `(𝔤, K)`-module `M`, a group `K` acts on `𝔤` through Lie algebra automorphisms `Ad k` and on
`M` compatibly with the action of `𝔤`, and the complex computing `H^n(𝔤, K; M)` consists of the
`K`-equivariant alternating maps `⋀ⁿ (𝔤 ⧸ 𝔨) → M`, where `𝔨` is the Lie algebra of `K`. Here
`K` is an arbitrary index type, with Lie algebra morphisms `ρ k : L → L` and linear maps
`σ k : M → M` such that `σ k ⁅x, m⁆ = ⁅ρ k x, σ k m⁆`. The equivariant relative cochains, those
with `ω (ρ k v₁, …, ρ k vₙ) = σ k (ω (v₁, …, vₙ))` for all `k`, again form a subcomplex, by the
naturality of the Chevalley–Eilenberg differential (`compLinearMap_d_eq_compAlternatingMap_d`).
For a `(𝔤, K)`-module the differentiated action of `K` is the action of `𝔨`, so `𝔨`-invariance
follows from `K`-equivariance, and this is the complex `C^•(𝔤, K; M) = Hom_K(⋀^• (𝔤 ⧸ 𝔨), M)` of
relative `(𝔤, K)`-cohomology, used to compute the cohomology of locally symmetric spaces. No Lie
group structure on `K` is needed to build the complex, so `𝔨`-invariance is imposed separately.
Both the relative and the equivariant relative complex are instances of `cochainSubcomplex`, the
subcomplex cut out by a family of submodules of cochains which the differential preserves.

In degree zero the relative cocycles are the `L`-invariant elements of `M`, so `H⁰(L, 𝔨; M)` is
the module `M^L` (`relativeCohomologyZeroEquiv`). This identification is adapted from Mathlib's
`groupCohomology.cocyclesIso₀`: it compares the categorical cycles with the kernel of the first
differential by `KernelFork.mapIsoOfIsLimit` against `cyclesIsKernel`.

## Main definitions

* `TauCeti.LieModule.Cohomology.cochainSubcomplex`: the subcomplex of the Chevalley–Eilenberg
  complex cut out by a family of submodules preserved by the differential, with its inclusion
  `TauCeti.LieModule.Cohomology.cochainSubcomplex.ι`.
* `TauCeti.LieModule.Cohomology.relativeCochains`: the relative cochains `C^n(L, 𝔨; M)`.
* `TauCeti.LieModule.Cohomology.relativeCochainComplex`: the relative cochain complex.
* `TauCeti.LieModule.Cohomology.relativeCohomology`: relative Lie algebra cohomology.
* `TauCeti.LieModule.Cohomology.equivariantRelativeCochains`,
  `TauCeti.LieModule.Cohomology.equivariantRelativeCochainComplex`,
  `TauCeti.LieModule.Cohomology.equivariantRelativeCohomology`: the `K`-equivariant relative
  cochains, their complex and its cohomology `H^n(𝔤, K; M)`.
* `TauCeti.LieModule.Cohomology.relativeCohomologyZeroEquiv`: `H⁰(L, 𝔨; M) ≃ M^L`.

## Main results

* `TauCeti.LieModule.Cohomology.d_mem_relativeCochains`: the differential preserves relative
  cochains.
* `TauCeti.LieModule.Cohomology.d_mem_equivariantRelativeCochains`: the differential preserves
  `K`-equivariant relative cochains.
* `TauCeti.LieModule.Cohomology.relativeCochains_bot`,
  `TauCeti.LieModule.Cohomology.relativeCochains_top_succ`: relative to `⊥` every cochain is
  relative, and relative to `⊤` there are no nonzero cochains in positive degree.

## References

* G. Hochschild and J.-P. Serre, *Cohomology of Lie algebras*, Ann. of Math. 57 (1953), 591–603.
* A. Borel and N. Wallach, *Continuous cohomology, discrete subgroups, and representations of
  reductive groups*, 2nd ed., Mathematical Surveys and Monographs 67, AMS, 2000, Chapter I.
-/

public section

open AlternatingMap CategoryTheory

namespace TauCeti.LieModule.Cohomology

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-! ### Subcomplexes of the Chevalley–Eilenberg complex -/

section Subcomplex

variable {M} (P : ∀ n : ℕ, Submodule R (L [⋀^Fin n]→ₗ[R] M))
  (hP : ∀ {n} {ω}, ω ∈ P n → d R L M n ω ∈ P (n + 1))

/-- The restriction of the Chevalley–Eilenberg differential to a family of submodules of cochains
which it preserves. -/
def restrictD (n : ℕ) : P n →ₗ[R] P (n + 1) :=
  (d R L M n).restrict fun _ ↦ hP

/-- The restricted differential is the Chevalley–Eilenberg differential. -/
@[simp]
theorem coe_restrictD_apply (n : ℕ) (ω : P n) :
    (restrictD P hP n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω :=
  (rfl)

/-- The restricted differential squares to zero. -/
theorem restrictD_comp_restrictD (n : ℕ) : restrictD P hP (n + 1) ∘ₗ restrictD P hP n = 0 := by
  ext ω : 2
  simp

/-- The subcomplex of the Chevalley–Eilenberg complex whose degree `n` term is `P n`, for a
family of submodules of cochains preserved by the differential. -/
@[expose] noncomputable def cochainSubcomplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (P n)) (fun n ↦ ModuleCat.ofHom (restrictD P hP n))
    fun n ↦ by rw [← ModuleCat.ofHom_comp, restrictD_comp_restrictD, ModuleCat.ofHom_zero]

/-- The degree `n` term of the subcomplex is `P n`. -/
@[simp]
theorem cochainSubcomplex_X (n : ℕ) : (cochainSubcomplex P hP).X n = ModuleCat.of R (P n) :=
  (rfl)

/-- The differential of the subcomplex from degree `n` to degree `n + 1`. -/
@[simp]
theorem cochainSubcomplex_d_succ (n : ℕ) :
    (cochainSubcomplex P hP).d n (n + 1) = ModuleCat.ofHom (restrictD P hP n) := by
  simp [cochainSubcomplex]

/-- The inclusion of the subcomplex into the Chevalley–Eilenberg complex. -/
noncomputable def cochainSubcomplex.ι : cochainSubcomplex P hP ⟶ cochainComplex R L M :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (P n).subtype) fun n ↦ by
    rw [cochainComplex_d_succ, cochainSubcomplex_d_succ]
    ext ω : 2
    -- Both composites send `ω` to `d ω`; `ModuleCat.hom_comp` does not fire because the objects
    -- are the terms of the complexes rather than `ModuleCat.of`.
    exact (coe_restrictD_apply P hP n ω).symm

/-- In each degree, the inclusion of the subcomplex is the inclusion of submodules. -/
@[simp]
theorem cochainSubcomplex.ι_f (n : ℕ) :
    (cochainSubcomplex.ι P hP).f n = ModuleCat.ofHom (P n).subtype :=
  (rfl)

end Subcomplex

/-! ### Cochains relative to a subalgebra -/

/-- The `n`-cochains of `L` relative to a Lie subalgebra `𝔨`, with coefficients in `M`: the
alternating maps which vanish as soon as one argument lies in `𝔨` and which are invariant under
the action of `𝔨`. They are the `𝔨`-equivariant alternating maps on `L ⧸ 𝔨`. -/
def relativeCochains (𝔨 : LieSubalgebra R L) (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) where
  carrier := {ω | (∀ (v : Fin n → L) (i : Fin n), v i ∈ 𝔨 → ω v = 0) ∧ ∀ x ∈ 𝔨, ⁅x, ω⁆ = 0}
  add_mem' {ω ω'} h h' :=
    ⟨fun v i hv ↦ by simp [h.1 v i hv, h'.1 v i hv], fun x hx ↦ by simp [h.2 x hx, h'.2 x hx]⟩
  zero_mem' := ⟨fun _ _ _ ↦ rfl, fun _ _ ↦ lie_zero _⟩
  smul_mem' c {ω} h := ⟨fun v i hv ↦ by simp [h.1 v i hv], fun x hx ↦ by simp [h.2 x hx]⟩

variable {M}

/-- Membership in the relative cochains, unfolded. -/
theorem mem_relativeCochains_iff {𝔨 : LieSubalgebra R L} {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ relativeCochains M 𝔨 n ↔
      (∀ (v : Fin n → L) (i : Fin n), v i ∈ 𝔨 → ω v = 0) ∧ ∀ x ∈ 𝔨, ⁅x, ω⁆ = 0 :=
  Iff.rfl

/-- A relative cochain vanishes when one of its arguments lies in `𝔨`. -/
theorem map_eq_zero_of_mem_relativeCochains {𝔨 : LieSubalgebra R L} {n : ℕ}
    {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ relativeCochains M 𝔨 n) {v : Fin n → L} {i : Fin n}
    (hv : v i ∈ 𝔨) : ω v = 0 :=
  hω.1 v i hv

/-- A relative cochain is invariant under the action of `𝔨`. -/
theorem lie_eq_zero_of_mem_relativeCochains {𝔨 : LieSubalgebra R L} {n : ℕ}
    {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ relativeCochains M 𝔨 n) {x : L} (hx : x ∈ 𝔨) :
    ⁅x, ω⁆ = 0 :=
  hω.2 x hx

/-- A relative cochain has vanishing interior products `ι_x ω` along `x ∈ 𝔨`. -/
theorem curryLeft_eq_zero_of_mem_relativeCochains {𝔨 : LieSubalgebra R L} {n : ℕ}
    {ω : L [⋀^Fin (n + 1)]→ₗ[R] M} (hω : ω ∈ relativeCochains M 𝔨 (n + 1)) {x : L}
    (hx : x ∈ 𝔨) : ω.curryLeft x = 0 := by
  ext w
  exact map_eq_zero_of_mem_relativeCochains hω (i := 0) (by simpa using hx)

/-- A `0`-cochain, that is an element `ω ![]` of `M`, is relative to `𝔨` exactly when it is
invariant under `𝔨`. -/
theorem mem_relativeCochains_zero_iff {𝔨 : LieSubalgebra R L} {ω : L [⋀^Fin 0]→ₗ[R] M} :
    ω ∈ relativeCochains M 𝔨 0 ↔ ∀ x ∈ 𝔨, ⁅x, ω ![]⁆ = 0 := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ⟨fun _ i ↦ i.elim0, fun x hx ↦ ?_⟩⟩
  · simpa using congr($(lie_eq_zero_of_mem_relativeCochains h hx) ![])
  ext v
  simp [Subsingleton.elim v ![], h x hx]

variable (M) in
/-- Relative to the zero subalgebra, every cochain is relative. -/
@[simp]
theorem relativeCochains_bot (n : ℕ) : relativeCochains M (⊥ : LieSubalgebra R L) n = ⊤ := by
  refine eq_top_iff.2 fun ω _ ↦ ⟨fun v i hv ↦ ω.map_coord_zero i ?_, fun x hx ↦ ?_⟩
  · simpa using hv
  · rw [(LieSubalgebra.mem_bot x).1 hx, zero_lie]

variable (M) in
/-- Relative to the whole Lie algebra, there are no nonzero cochains in positive degree. -/
@[simp]
theorem relativeCochains_top_succ (n : ℕ) :
    relativeCochains M (⊤ : LieSubalgebra R L) (n + 1) = ⊥ :=
  eq_bot_iff.2 fun ω hω ↦ by
    ext v
    exact map_eq_zero_of_mem_relativeCochains hω (i := 0) (LieSubalgebra.mem_top _)

/-- The Chevalley–Eilenberg differential sends relative cochains to relative cochains: by
Cartan's formula `ι_x d ω = ⁅x, ω⁆ - d ι_x ω`, both terms vanish for `x ∈ 𝔨`, and `d` commutes
with the action of `𝔨`. -/
theorem d_mem_relativeCochains {𝔨 : LieSubalgebra R L} {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ relativeCochains M 𝔨 n) : d R L M n ω ∈ relativeCochains M 𝔨 (n + 1) := by
  refine ⟨fun v i hv ↦ map_eq_zero_of_curryLeft_eq_zero ?_ (rfl : v i = v i), fun x hx ↦ ?_⟩
  · cases n with
    | zero => rw [curryLeft_d_zero, lie_eq_zero_of_mem_relativeCochains hω hv]
    | succ n =>
      rw [curryLeft_d_succ, lie_eq_zero_of_mem_relativeCochains hω hv,
        curryLeft_eq_zero_of_mem_relativeCochains hω hv, _root_.map_zero, sub_zero]
  · rw [lie_d, lie_eq_zero_of_mem_relativeCochains hω hx, _root_.map_zero]

variable (M)

/-- The cochain complex of `L` relative to `𝔨` with coefficients in `M`, whose degree `n` term
is the module of relative `n`-cochains. -/
noncomputable abbrev relativeCochainComplex (𝔨 : LieSubalgebra R L) :
    CochainComplex (ModuleCat R) ℕ :=
  cochainSubcomplex (relativeCochains M 𝔨) d_mem_relativeCochains

/-- The `n`-th Lie algebra cohomology of `L` relative to `𝔨` with coefficients in `M`, the
homology of the relative cochain complex in degree `n`. -/
noncomputable abbrev relativeCohomology (𝔨 : LieSubalgebra R L) (n : ℕ) : ModuleCat R :=
  (relativeCochainComplex M 𝔨).homology n

/-! ### Relative cohomology in degree zero -/

/-- The relative `0`-cocycles are the `L`-invariant elements of `M`: a `0`-cochain `ω` is a
cocycle exactly when `⁅x, ω ![]⁆ = 0` for every `x : L`. -/
def kerRelativeDZeroEquiv (𝔨 : LieSubalgebra R L) :
    LinearMap.ker (restrictD (relativeCochains M 𝔨) d_mem_relativeCochains 0) ≃ₗ[R]
      LieModule.maxTrivSubmodule R L M where
  toFun ω := ⟨(ω : L [⋀^Fin 0]→ₗ[R] M) ![], (LieModule.mem_maxTrivSubmodule R L M _).2 fun x ↦ by
    have h : d R L M 0 ω = 0 :=
      (coe_restrictD_apply (relativeCochains M 𝔨) d_mem_relativeCochains 0 ω).symm.trans
        (congrArg Subtype.val (LinearMap.mem_ker.1 ω.property))
    simpa using congr($h ![x])⟩
  invFun m :=
    ⟨⟨constOfIsEmpty R L (Fin 0) (m : M), mem_relativeCochains_zero_iff.2 fun x _ ↦ by
      simpa using (LieModule.mem_maxTrivSubmodule R L M m).1 m.property x⟩,
      LinearMap.mem_ker.2 <| by
        ext v
        simpa using (LieModule.mem_maxTrivSubmodule R L M m).1 m.property (v 0)⟩
  map_add' ω ω' := rfl
  map_smul' c ω := rfl
  left_inv ω := by
    ext v
    simp [Subsingleton.elim v ![]]
  right_inv _ := rfl

/-- A relative `0`-cocycle `ω` corresponds to the invariant element `ω ![]`. -/
@[simp]
theorem coe_kerRelativeDZeroEquiv_apply (𝔨 : LieSubalgebra R L)
    (ω : LinearMap.ker (restrictD (relativeCochains M 𝔨) d_mem_relativeCochains 0)) :
    (kerRelativeDZeroEquiv M 𝔨 ω : M) = (ω : L [⋀^Fin 0]→ₗ[R] M) ![] :=
  (rfl)

/-- An invariant element `m` corresponds to the constant `0`-cocycle with value `m`. -/
@[simp]
theorem coe_kerRelativeDZeroEquiv_symm_apply (𝔨 : LieSubalgebra R L)
    (m : LieModule.maxTrivSubmodule R L M) :
    (((kerRelativeDZeroEquiv M 𝔨).symm m : relativeCochains M 𝔨 0) : L [⋀^Fin 0]→ₗ[R] M) =
      constOfIsEmpty R L (Fin 0) (m : M) :=
  (rfl)

/-- The relative `0`-cycles in the categorical sense are the kernel of the first differential. -/
private noncomputable def relativeCyclesZeroIso (𝔨 : LieSubalgebra R L) :
    (relativeCochainComplex M 𝔨).cycles 0 ≅
      ModuleCat.of R (LinearMap.ker (restrictD (relativeCochains M 𝔨) d_mem_relativeCochains 0)) :=
  let S : ShortComplex (ModuleCat R) :=
    .mk (ModuleCat.ofHom
        (LinearMap.ker (restrictD (relativeCochains M 𝔨) d_mem_relativeCochains 0)).subtype)
      (ModuleCat.ofHom (restrictD (relativeCochains M 𝔨) d_mem_relativeCochains 0))
      (by ext ω : 2; exact ω.property)
  haveI : Mono S.f :=
    (ModuleCat.mono_iff_injective _).2 (Submodule.injective_subtype _)
  Limits.KernelFork.mapIsoOfIsLimit
    ((relativeCochainComplex M 𝔨).cyclesIsKernel 0 1 (by simp))
    (S.moduleCat_exact_iff.2 fun ω hω ↦ ⟨⟨ω, hω⟩, rfl⟩).fIsKernel
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) <| by
      rw [cochainSubcomplex_d_succ]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

private theorem relativeCyclesZeroIso_hom_comp (𝔨 : LieSubalgebra R L) :
    (relativeCyclesZeroIso M 𝔨).hom ≫ ModuleCat.ofHom
        (LinearMap.ker (restrictD (relativeCochains M 𝔨) d_mem_relativeCochains 0)).subtype =
      (relativeCochainComplex M 𝔨).iCycles 0 := by
  simp only [relativeCyclesZeroIso, Limits.KernelFork.mapIsoOfIsLimit_hom]
  exact (Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)

/-- **Relative cohomology in degree zero**: `H⁰(L, 𝔨; M)` is the module `M^L` of `L`-invariant
elements of `M`. -/
noncomputable def relativeCohomologyZeroEquiv (𝔨 : LieSubalgebra R L) :
    relativeCohomology M 𝔨 0 ≃ₗ[R] LieModule.maxTrivSubmodule R L M :=
  ((CochainComplex.isoHomologyπ₀ _).symm ≪≫ relativeCyclesZeroIso M 𝔨).toLinearEquiv ≪≫ₗ
    kerRelativeDZeroEquiv M 𝔨

/-- The class of a relative `0`-cocycle `z` corresponds to the invariant element `z ![]`. -/
@[simp]
theorem relativeCohomologyZeroEquiv_homologyπ_apply (𝔨 : LieSubalgebra R L)
    (z : (relativeCochainComplex M 𝔨).cycles 0) :
    (relativeCohomologyZeroEquiv M 𝔨 ((relativeCochainComplex M 𝔨).homologyπ 0 z) : M) =
      ((relativeCochains M 𝔨 0).subtype ∘ₗ ((relativeCochainComplex M 𝔨).iCycles 0).hom) z ![] := by
  have h₁ := congr(ModuleCat.Hom.hom $(relativeCyclesZeroIso_hom_comp M 𝔨) z)
  have h₂ : (relativeCochainComplex M 𝔨).isoHomologyπ₀.inv
      ((relativeCochainComplex M 𝔨).homologyπ 0 z) = z :=
    (relativeCochainComplex M 𝔨).isoHomologyπ₀.hom_inv_id_apply z
  rw [relativeCohomologyZeroEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply]
  -- `h₁` identifies the two cochains as elements of `(relativeCochainComplex M 𝔨).X 0`, whose
  -- carrier is `relativeCochains M 𝔨 0` by `cochainSubcomplex_X`.
  simp only [Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, coe_kerRelativeDZeroEquiv_apply, h₂]
  exact congrArg (fun ω : relativeCochains M 𝔨 0 ↦ (ω : L [⋀^Fin 0]→ₗ[R] M) ![]) h₁

/-- An invariant element `m` corresponds to the class of any relative `0`-cocycle `z` with
`z ![] = m`. -/
theorem relativeCohomologyZeroEquiv_symm_apply (𝔨 : LieSubalgebra R L)
    (m : LieModule.maxTrivSubmodule R L M) (z : (relativeCochainComplex M 𝔨).cycles 0)
    (hz : ((relativeCochains M 𝔨 0).subtype ∘ₗ ((relativeCochainComplex M 𝔨).iCycles 0).hom) z
      ![] = m) :
    (relativeCohomologyZeroEquiv M 𝔨).symm m = (relativeCochainComplex M 𝔨).homologyπ 0 z :=
  (LinearEquiv.symm_apply_eq _).2 <| Subtype.ext <| by
    rw [relativeCohomologyZeroEquiv_homologyπ_apply, hz]

/-! ### Equivariant relative cochains -/

variable {K : Type*}

/-- The `n`-cochains of `L` relative to `𝔨` which are equivariant for a family of pairs of maps
`ρ k : L → L` and `σ k : M → M` indexed by `k : K`:
`ω (ρ k v₁, …, ρ k vₙ) = σ k (ω (v₁, …, vₙ))`. For a `(𝔤, K)`-module, with `ρ` the adjoint action
of `K` on `𝔤`, `σ` the action of `K` on `M` and `𝔨` the Lie algebra of `K`, these are the cochains
`C^n(𝔤, K; M) = Hom_K(⋀ⁿ (𝔤 ⧸ 𝔨), M)`. -/
def equivariantRelativeCochains (𝔨 : LieSubalgebra R L) (ρ : K → L →ₗ⁅R⁆ L)
    (σ : K → M →ₗ[R] M) (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  relativeCochains M 𝔨 n ⊓
    { carrier := {ω | ∀ (k : K) (v : Fin n → L), ω (fun i ↦ ρ k (v i)) = σ k (ω v)}
      add_mem' {ω ω'} h h' k v := by simp [h k v, h' k v]
      zero_mem' k v := by simp
      smul_mem' c {ω} h k v := by simp [h k v] }

variable {M}

/-- Membership in the equivariant relative cochains, unfolded. -/
theorem mem_equivariantRelativeCochains_iff {𝔨 : LieSubalgebra R L} {ρ : K → L →ₗ⁅R⁆ L}
    {σ : K → M →ₗ[R] M} {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ equivariantRelativeCochains M 𝔨 ρ σ n ↔ ω ∈ relativeCochains M 𝔨 n ∧
      ∀ (k : K) (v : Fin n → L), ω (fun i ↦ ρ k (v i)) = σ k (ω v) :=
  Iff.rfl

/-- The differential sends equivariant relative cochains to equivariant relative cochains,
provided each `σ k` intertwines the action of `x` with that of `ρ k x`. -/
theorem d_mem_equivariantRelativeCochains {𝔨 : LieSubalgebra R L} {ρ : K → L →ₗ⁅R⁆ L}
    {σ : K → M →ₗ[R] M} (hσ : ∀ k x m, σ k ⁅x, m⁆ = ⁅ρ k x, σ k m⁆) {n : ℕ}
    {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ equivariantRelativeCochains M 𝔨 ρ σ n) :
    d R L M n ω ∈ equivariantRelativeCochains M 𝔨 ρ σ (n + 1) := by
  refine ⟨d_mem_relativeCochains hω.1, fun k v ↦ ?_⟩
  have h : ω.compLinearMap (ρ k : L →ₗ[R] L) = (σ k).compAlternatingMap ω := by
    ext w
    exact hω.2 k w
  simpa using congr($(compLinearMap_d_eq_compAlternatingMap_d (ρ k) (hσ k) h) v)

variable (M)

/-- The equivariant relative cochain complex of `L` relative to `𝔨` with coefficients in `M`;
for a `(𝔤, K)`-module, the complex `C^•(𝔤, K; M)`. -/
noncomputable abbrev equivariantRelativeCochainComplex (𝔨 : LieSubalgebra R L)
    {ρ : K → L →ₗ⁅R⁆ L} {σ : K → M →ₗ[R] M} (hσ : ∀ k x m, σ k ⁅x, m⁆ = ⁅ρ k x, σ k m⁆) :
    CochainComplex (ModuleCat R) ℕ :=
  cochainSubcomplex (equivariantRelativeCochains M 𝔨 ρ σ) (d_mem_equivariantRelativeCochains hσ)

/-- The `n`-th equivariant relative Lie algebra cohomology of `L` relative to `𝔨` with
coefficients in `M`; for a `(𝔤, K)`-module, the relative cohomology `H^n(𝔤, K; M)`. -/
noncomputable abbrev equivariantRelativeCohomology (𝔨 : LieSubalgebra R L)
    {ρ : K → L →ₗ⁅R⁆ L} {σ : K → M →ₗ[R] M} (hσ : ∀ k x m, σ k ⁅x, m⁆ = ⁅ρ k x, σ k m⁆)
    (n : ℕ) : ModuleCat R :=
  (equivariantRelativeCochainComplex M 𝔨 hσ).homology n

/-- With no equivariance condition, the equivariant relative cochains are the relative
cochains. -/
@[simp]
theorem equivariantRelativeCochains_of_isEmpty [IsEmpty K] (𝔨 : LieSubalgebra R L)
    (ρ : K → L →ₗ⁅R⁆ L) (σ : K → M →ₗ[R] M) (n : ℕ) :
    equivariantRelativeCochains M 𝔨 ρ σ n = relativeCochains M 𝔨 n :=
  inf_eq_left.2 fun _ _ k ↦ isEmptyElim k

end TauCeti.LieModule.Cohomology
