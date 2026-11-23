/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.Cohomology.Map
public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.LinearAlgebra.Alternating.Conormal

/-!
# Relative Lie algebra cohomology

Let `L` be a Lie algebra over a commutative ring `R`, `H ⊆ L` a Lie subalgebra and `M` an
`L`-module. The relative cochains of the pair `(L, H)` are the Chevalley–Eilenberg cochains
`ω : L [⋀^Fin n]→ₗ[R] M` that vanish as soon as one argument lies in `H` (they are conormal to
`H`, `Submodule.conormalForms`) and are annihilated by the Lie derivatives `⁅y, ω⁆` along
`y ∈ H`. Pulling back along `L → L ⧸ H` identifies them with the `H`-invariant alternating maps
on `L ⧸ H` (`relativeCochainsEquiv`), that is, with `Hom_H(⋀ⁿ(L/H), M)`. By Cartan's formula
`ι_y d ω = ⁅y, ω⁆ - d ι_y ω` and the `L`-equivariance of the differential, the relative cochains
form a subcomplex of the Chevalley–Eilenberg complex, the relative complex `C^•(L, H; M)`; its
cohomology is the relative Lie algebra cohomology `H^•(L, H; M)`.

In degree zero the relative cocycles are the `L`-invariant elements of `M`, so `H⁰(L, H; M)` is
the module `M^L` (`relativeCohomologyZeroEquiv`). This identification is adapted from Mathlib's
`groupCohomology.cocyclesIso₀`: it compares the categorical cycles with the kernel of the first
differential by `KernelFork.mapIsoOfIsLimit` against `cyclesIsKernel`.

For a `(𝔤, K)`-module `M`, a group `K` acts on `𝔤` through Lie algebra automorphisms `Ad k` and on
`M` compatibly, `ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆`, and the complex computing `H^n(𝔤, K; M)` consists
of the `K`-equivariant alternating maps on `𝔤 ⧸ 𝔨`. Here `K` is an arbitrary index type, with Lie
algebra morphisms `Ad k : L → L` and linear maps `ρ k : M → M` satisfying this compatibility; for
a group `K` acting through representations, take the Lie algebra morphisms
`Representation.toLieHom`. The `K`-equivariant relative cochains, those with
`ω (Ad k v₁, …, Ad k vₙ) = ρ k (ω (v₁, …, vₙ))`, again form a subcomplex, by the naturality of the
differential (`compLinearMap_d_eq_compAlternatingMap_d`). When `𝔨` is `Ad(K)`-stable, they are
`Hom_K(⋀ⁿ(𝔤/𝔨), M)` with `𝔨`-invariance imposed. When moreover `K` is a Lie group with Lie algebra
`𝔨` and `M` is a `(𝔤, K)`-module, `K`-equivariance implies `𝔨`-invariance, and this is the relative
complex `C^•(𝔤, K; M)` of the pair `(𝔤, K)`. No Lie group structure on `K` is needed to build the
complex, so here `𝔨` is a separate datum and the `𝔨`-invariance is imposed. For `K` disconnected,
as for `O(2)` inside `GL₂(ℝ)`, the `K`-equivariance cuts out more than the `𝔨`-invariance does.

## Main definitions

* `TauCeti.LieModule.Cohomology.cochainSubcomplex`: the subcomplex of the Chevalley–Eilenberg
  complex on a family of submodules of cochains stable under the differential.
* `TauCeti.LieModule.Cohomology.relativeCochains`: the relative cochains of a pair `(L, H)`.
* `TauCeti.LieModule.Cohomology.relativeCochainComplex`,
  `TauCeti.LieModule.Cohomology.relativeCohomology`: the relative complex and its cohomology.
* `TauCeti.LieModule.Cohomology.relativeCochainsEquiv`: relative cochains are the `H`-invariant
  alternating maps on `L ⧸ H`.
* `TauCeti.LieModule.Cohomology.equivariantRelativeCochains`,
  `TauCeti.LieModule.Cohomology.equivariantRelativeCochainComplex`,
  `TauCeti.LieModule.Cohomology.equivariantRelativeCohomology`: the complex of `K`-equivariant
  relative cochains and its cohomology, the relative complex of a pair `(𝔤, K)` when `𝔨` is the
  `Ad(K)`-stable Lie algebra of a Lie group `K` and `M` is a `(𝔤, K)`-module.
* `TauCeti.LieModule.Cohomology.relativeCohomologyZeroEquiv`: `H⁰(L, H; M) ≃ M^L`.

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
* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*,
  Trans. Amer. Math. Soc. 63 (1948), 85–124, §§22–23.
* A. Borel and N. Wallach, *Continuous cohomology, discrete subgroups, and representations of
  reductive groups*, second edition, Mathematical Surveys and Monographs 67, American
  Mathematical Society, 2000, §I.1.1.
* G. Harder and A. Raghuram, *Eisenstein cohomology for GL_N and the special values of
  Rankin–Selberg L-functions*, Annals of Mathematics Studies 203, Princeton University Press,
  2020, §3.1.1.
-/

public section

open AlternatingMap CategoryTheory

namespace TauCeti.LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-! ### Subcomplexes of the Chevalley–Eilenberg complex -/

section Subcomplex

variable (S : ∀ n, Submodule R (L [⋀^Fin n]→ₗ[R] M))
  (hS : ∀ n, ∀ ω ∈ S n, d R L M n ω ∈ S (n + 1))

/-- The differential restricted to a family of submodules of cochains stable under it. -/
def cochainSubcomplexD (n : ℕ) : S n →ₗ[R] S (n + 1) :=
  (d R L M n).restrict (hS n)

@[simp]
theorem coe_cochainSubcomplexD {n : ℕ} (ω : S n) :
    (cochainSubcomplexD S hS n ω : L [⋀^Fin (n + 1)]→ₗ[R] M) = d R L M n ω :=
  (rfl)

theorem cochainSubcomplexD_comp_cochainSubcomplexD (n : ℕ) :
    cochainSubcomplexD S hS (n + 1) ∘ₗ cochainSubcomplexD S hS n = 0 :=
  LinearMap.ext fun ω ↦ Subtype.ext (d_d n ω.val)

/-- The subcomplex of the Chevalley–Eilenberg complex on a family of submodules of cochains
stable under the differential. -/
@[expose] noncomputable def cochainSubcomplex : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of R (S n))
    (fun n ↦ ModuleCat.ofHom (cochainSubcomplexD S hS n)) fun n ↦ by
      rw [← ModuleCat.ofHom_comp, cochainSubcomplexD_comp_cochainSubcomplexD,
        ModuleCat.ofHom_zero]

@[simp]
theorem cochainSubcomplex_X (n : ℕ) :
    (cochainSubcomplex S hS).X n = ModuleCat.of R (S n) :=
  (rfl)

@[simp]
theorem cochainSubcomplex_d_succ (n : ℕ) :
    (cochainSubcomplex S hS).d n (n + 1) = ModuleCat.ofHom (cochainSubcomplexD S hS n) := by
  simp [cochainSubcomplex]

/-- The inclusion of two subcomplexes of the Chevalley–Eilenberg complex. -/
noncomputable def cochainSubcomplexInclusion {S' : ∀ n, Submodule R (L [⋀^Fin n]→ₗ[R] M)}
    (hS' : ∀ n, ∀ ω ∈ S' n, d R L M n ω ∈ S' (n + 1)) (h : ∀ n, S n ≤ S' n) :
    cochainSubcomplex S hS ⟶ cochainSubcomplex S' hS' :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (Submodule.inclusion (h n))) fun n ↦ by
    rw [cochainSubcomplex_d_succ, cochainSubcomplex_d_succ]
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

@[simp]
theorem cochainSubcomplexInclusion_f {S' : ∀ n, Submodule R (L [⋀^Fin n]→ₗ[R] M)}
    (hS' : ∀ n, ∀ ω ∈ S' n, d R L M n ω ∈ S' (n + 1)) (h : ∀ n, S n ≤ S' n) (n : ℕ) :
    (cochainSubcomplexInclusion S hS hS' h).f n = ModuleCat.ofHom (Submodule.inclusion (h n)) :=
  (rfl)

/-- The inclusion of a subcomplex into the Chevalley–Eilenberg complex. -/
noncomputable def cochainSubcomplexSubtype : cochainSubcomplex S hS ⟶ cochainComplex R L M :=
  CochainComplex.ofHom (fun n ↦ ModuleCat.ofHom (S n).subtype) fun n ↦ by
    rw [cochainSubcomplex_d_succ, cochainComplex_d_succ]
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

@[simp]
theorem cochainSubcomplexSubtype_f (n : ℕ) :
    (cochainSubcomplexSubtype S hS).f n = ModuleCat.ofHom (S n).subtype :=
  (rfl)

/-- The inclusion of subcomplexes commutes with their inclusions into the Chevalley–Eilenberg
complex. -/
@[simp]
theorem cochainSubcomplexInclusion_comp_subtype {S' : ∀ n, Submodule R (L [⋀^Fin n]→ₗ[R] M)}
    (hS' : ∀ n, ∀ ω ∈ S' n, d R L M n ω ∈ S' (n + 1)) (h : ∀ n, S n ≤ S' n) :
    cochainSubcomplexInclusion S hS hS' h ≫ cochainSubcomplexSubtype S' hS' =
      cochainSubcomplexSubtype S hS := by
  ext n : 2
  rfl

end Subcomplex

/-! ### The relative complex of a pair `(L, H)` -/

section Relative

variable (R M) (H : LieSubalgebra R L)

/-- The relative `n`-cochains of the pair `(L, H)`: the cochains that vanish as soon as one
argument lies in `H` and are annihilated by the Lie derivatives along `H`. These are the
`H`-invariant alternating maps on `L ⧸ H` (`relativeCochainsEquiv`). -/
def relativeCochains (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  H.toLieSubmodule.toSubmodule.conormalForms (Fin n) M ⊓
    (LieModule.maxTrivSubmodule R H (L [⋀^Fin n]→ₗ[R] M)).toSubmodule

variable {R M H}

@[simp]
theorem mem_relativeCochains_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ relativeCochains R M H n ↔
      (∀ (v : Fin n → L) (i : Fin n), v i ∈ H → ω v = 0) ∧ ∀ y ∈ H, ⁅y, ω⁆ = 0 :=
  Submodule.mem_inf.trans <| and_congr (by simp) <| by
    simp only [LieSubmodule.mem_toSubmodule, LieModule.mem_maxTrivSubmodule, Subtype.forall,
      LieSubalgebra.coe_bracket_of_module]

/-- In positive degree, the first condition on relative cochains says that the interior
products along `H` vanish. -/
theorem mem_relativeCochains_succ_iff {n : ℕ} {ω : L [⋀^Fin (n + 1)]→ₗ[R] M} :
    ω ∈ relativeCochains R M H (n + 1) ↔
      (∀ y ∈ H, ω.curryLeft y = 0) ∧ ∀ y ∈ H, ⁅y, ω⁆ = 0 := by
  rw [mem_relativeCochains_iff]
  refine and_congr_left' ⟨fun h y hy ↦ ?_, fun h v i hv ↦
    map_eq_zero_of_curryLeft_eq_zero (h _ hv) rfl⟩
  ext w
  rw [curryLeft_apply_apply, zero_apply]
  exact h _ 0 (by simpa using hy)

/-- A relative `0`-cochain is an element of `M` annihilated by `H`. -/
theorem mem_relativeCochains_zero_iff {ω : L [⋀^Fin 0]→ₗ[R] M} :
    ω ∈ relativeCochains R M H 0 ↔ ∀ y ∈ H, ⁅y, ω ![]⁆ = 0 := by
  rw [mem_relativeCochains_iff]
  refine ⟨fun h y hy ↦ ?_, fun h ↦ ⟨fun _ i ↦ i.elim0, fun y hy ↦ ?_⟩⟩
  · simpa using congr($(h.2 y hy) ![])
  · ext v
    simp [Subsingleton.elim v ![], h y hy]

/-- Relative to the zero subalgebra, every cochain is relative. -/
@[simp]
theorem relativeCochains_bot (n : ℕ) : relativeCochains R M (⊥ : LieSubalgebra R L) n = ⊤ := by
  refine eq_top_iff.mpr fun ω _ ↦ ⟨?_, (LieSubmodule.mem_toSubmodule _).mpr <|
    (LieModule.mem_maxTrivSubmodule R _ _ ω).mpr fun y ↦ ?_⟩
  · have h : (⊥ : LieSubalgebra R L).toLieSubmodule.toSubmodule = ⊥ := by ext; simp
    rw [h, Submodule.conormalForms_bot]
    exact Submodule.mem_top
  · rw [LieSubalgebra.coe_bracket_of_module, (LieSubalgebra.mem_bot (y : L)).mp y.property,
      zero_lie]

/-- Relative to the whole Lie algebra, there are no nonzero cochains in positive degree. -/
@[simp]
theorem relativeCochains_top_succ (n : ℕ) :
    relativeCochains R M (⊤ : LieSubalgebra R L) (n + 1) = ⊥ :=
  eq_bot_iff.mpr fun _ hω ↦ (Submodule.mem_bot R).mpr <| by
    ext v
    exact (mem_relativeCochains_iff.mp hω).1 v 0 (LieSubalgebra.mem_top _)

/-- **The differential preserves relative cochains**, by Cartan's formula
`ι_y d ω = ⁅y, ω⁆ - d ι_y ω` and the equivariance `⁅y, d ω⁆ = d ⁅y, ω⁆`. -/
theorem d_mem_relativeCochains {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ relativeCochains R M H n) : d R L M n ω ∈ relativeCochains R M H (n + 1) := by
  have hlie := (mem_relativeCochains_iff.mp hω).2
  refine mem_relativeCochains_succ_iff.mpr ⟨fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · cases n with
    | zero => rw [curryLeft_d_zero, hlie y hy]
    | succ n =>
      rw [curryLeft_d_succ, hlie y hy, (mem_relativeCochains_succ_iff.mp hω).1 y hy,
        _root_.map_zero, sub_zero]
  · rw [lie_d, hlie y hy, _root_.map_zero]

variable (R M H)

/-- The relative Chevalley–Eilenberg complex `C^•(L, H; M)` of the pair `(L, H)`. -/
noncomputable abbrev relativeCochainComplex : CochainComplex (ModuleCat R) ℕ :=
  cochainSubcomplex (relativeCochains R M H) fun _ _ ↦ d_mem_relativeCochains

/-- The `n`-th relative Lie algebra cohomology `H^n(L, H; M)` of the pair `(L, H)`. -/
noncomputable abbrev relativeCohomology (n : ℕ) : ModuleCat R :=
  (relativeCochainComplex R M H).homology n

/-! ### Relative cohomology in degree zero -/

/-- The relative `0`-cocycles are the `L`-invariant elements of `M`: a `0`-cochain `ω` is a
cocycle exactly when `⁅x, ω ![]⁆ = 0` for every `x : L`. -/
def kerRelativeDZeroEquiv :
    LinearMap.ker (cochainSubcomplexD (relativeCochains R M H)
        (fun _ _ ↦ d_mem_relativeCochains) 0) ≃ₗ[R]
      LieModule.maxTrivSubmodule R L M where
  toFun ω := ⟨(ω : L [⋀^Fin 0]→ₗ[R] M) ![], (LieModule.mem_maxTrivSubmodule R L M _).mpr
    fun x ↦ by
      have h : d R L M 0 ω = 0 :=
        (coe_cochainSubcomplexD (relativeCochains R M H) (fun _ _ ↦ d_mem_relativeCochains)
          ω.val).symm.trans (congrArg Subtype.val (LinearMap.mem_ker.mp ω.property))
      simpa using congr($h ![x])⟩
  invFun m :=
    ⟨⟨constOfIsEmpty R L (Fin 0) (m : M), mem_relativeCochains_zero_iff.mpr fun x _ ↦ by
      simpa using (LieModule.mem_maxTrivSubmodule R L M m).mp m.property x⟩,
      LinearMap.mem_ker.mpr <| by
        ext v
        simpa using (LieModule.mem_maxTrivSubmodule R L M m).mp m.property (v 0)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv ω := by
    ext v
    simp [Subsingleton.elim v ![]]
  right_inv _ := rfl

/-- A relative `0`-cocycle `ω` corresponds to the invariant element `ω ![]`. -/
@[simp]
theorem coe_kerRelativeDZeroEquiv_apply
    (ω : LinearMap.ker (cochainSubcomplexD (relativeCochains R M H)
      (fun _ _ ↦ d_mem_relativeCochains) 0)) :
    (kerRelativeDZeroEquiv R M H ω : M) = (ω : L [⋀^Fin 0]→ₗ[R] M) ![] :=
  (rfl)

/-- An invariant element `m` corresponds to the constant `0`-cocycle with value `m`. -/
@[simp]
theorem coe_kerRelativeDZeroEquiv_symm_apply (m : LieModule.maxTrivSubmodule R L M) :
    (((kerRelativeDZeroEquiv R M H).symm m : relativeCochains R M H 0) :
        L [⋀^Fin 0]→ₗ[R] M) =
      constOfIsEmpty R L (Fin 0) (m : M) :=
  (rfl)

/-- The relative `0`-cycles in the categorical sense are the kernel of the first differential. -/
private noncomputable def relativeCyclesZeroIso :
    (relativeCochainComplex R M H).cycles 0 ≅
      ModuleCat.of R (LinearMap.ker (cochainSubcomplexD (relativeCochains R M H)
        (fun _ _ ↦ d_mem_relativeCochains) 0)) :=
  let D := cochainSubcomplexD (relativeCochains R M H) (fun _ _ ↦ d_mem_relativeCochains) 0
  let S : ShortComplex (ModuleCat R) :=
    .mk (ModuleCat.ofHom (LinearMap.ker D).subtype) (ModuleCat.ofHom D)
      (by ext ω : 2; exact ω.property)
  haveI : Mono S.f :=
    (ModuleCat.mono_iff_injective _).mpr (Submodule.injective_subtype _)
  Limits.KernelFork.mapIsoOfIsLimit
    ((relativeCochainComplex R M H).cyclesIsKernel 0 1 (by simp))
    (S.moduleCat_exact_iff.mpr fun ω hω ↦ ⟨⟨ω, hω⟩, rfl⟩).fIsKernel
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) <| by
      rw [cochainSubcomplex_d_succ]
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

private theorem relativeCyclesZeroIso_hom_comp :
    (relativeCyclesZeroIso R M H).hom ≫ ModuleCat.ofHom
        (LinearMap.ker (cochainSubcomplexD (relativeCochains R M H)
          (fun _ _ ↦ d_mem_relativeCochains) 0)).subtype =
      (relativeCochainComplex R M H).iCycles 0 := by
  simp only [relativeCyclesZeroIso, Limits.KernelFork.mapIsoOfIsLimit_hom]
  exact (Limits.KernelFork.mapOfIsLimit_ι _ _ _).trans (Category.comp_id _)

/-- **Relative cohomology in degree zero**: `H⁰(L, H; M)` is the module `M^L` of `L`-invariant
elements of `M`. -/
noncomputable def relativeCohomologyZeroEquiv :
    relativeCohomology R M H 0 ≃ₗ[R] LieModule.maxTrivSubmodule R L M :=
  ((CochainComplex.isoHomologyπ₀ _).symm ≪≫ relativeCyclesZeroIso R M H).toLinearEquiv ≪≫ₗ
    kerRelativeDZeroEquiv R M H

/-- The class of a relative `0`-cocycle `z` corresponds to the invariant element `z ![]`. -/
@[simp]
theorem relativeCohomologyZeroEquiv_homologyπ_apply (z : (relativeCochainComplex R M H).cycles 0) :
    (relativeCohomologyZeroEquiv R M H ((relativeCochainComplex R M H).homologyπ 0 z) : M) =
      ((relativeCochains R M H 0).subtype ∘ₗ ((relativeCochainComplex R M H).iCycles 0).hom) z
        ![] := by
  have h₁ := congr(ModuleCat.Hom.hom $(relativeCyclesZeroIso_hom_comp R M H) z)
  have h₂ : (relativeCochainComplex R M H).isoHomologyπ₀.inv
      ((relativeCochainComplex R M H).homologyπ 0 z) = z :=
    (relativeCochainComplex R M H).isoHomologyπ₀.hom_inv_id_apply z
  rw [relativeCohomologyZeroEquiv, LinearEquiv.trans_apply, Iso.toLinearEquiv_apply]
  -- `h₁` identifies the two cochains as elements of `(relativeCochainComplex R M H).X 0`, whose
  -- carrier is `relativeCochains R M H 0` by `cochainSubcomplex_X`.
  simp only [Iso.trans_hom, Iso.symm_hom, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, coe_kerRelativeDZeroEquiv_apply, h₂]
  exact congrArg (fun ω : relativeCochains R M H 0 ↦ (ω : L [⋀^Fin 0]→ₗ[R] M) ![]) h₁

/-- An invariant element `m` corresponds to the class of any relative `0`-cocycle `z` with
`z ![] = m`. -/
theorem relativeCohomologyZeroEquiv_symm_apply (m : LieModule.maxTrivSubmodule R L M)
    (z : (relativeCochainComplex R M H).cycles 0)
    (hz : ((relativeCochains R M H 0).subtype ∘ₗ ((relativeCochainComplex R M H).iCycles 0).hom)
      z ![] = m) :
    (relativeCohomologyZeroEquiv R M H).symm m = (relativeCochainComplex R M H).homologyπ 0 z :=
  (LinearEquiv.symm_apply_eq _).mpr <| Subtype.ext <| by
    rw [relativeCohomologyZeroEquiv_homologyπ_apply, hz]

/-! ### Relative cochains as invariant alternating maps on the quotient -/

variable {R M H} in
/-- Pulling back along `L → L ⧸ H` intertwines the action of `y ∈ H` on alternating maps on
`L ⧸ H` with the action of `y` on cochains of `L`. -/
theorem lie_compLinearMap_mk' {n : ℕ} (y : H)
    (η : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) :
    ⁅(y : L), η.compLinearMap (LieSubmodule.Quotient.mk' H.toLieSubmodule : L →ₗ[R] _)⁆ =
      ⁅y, η⁆.compLinearMap (LieSubmodule.Quotient.mk' H.toLieSubmodule : L →ₗ[R] _) := by
  ext v
  simp only [lie_apply, compLinearMap_apply]
  congr 2
  refine funext fun i ↦ congrArg η (funext fun j ↦ ?_)
  rcases eq_or_ne j i with rfl | hj
  · simpa using (LieSubmodule.Quotient.mk' H.toLieSubmodule).map_lie y (v j)
  · simp [Function.update_of_ne hj]

variable {R M H} in
/-- The pullback of an `H`-invariant alternating map on `L ⧸ H` is a relative cochain. -/
theorem compLinearMap_mk'_mem_relativeCochains {n : ℕ}
    (η : LieModule.maxTrivSubmodule R H ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)) :
    (η : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M).compLinearMap
      (LieSubmodule.Quotient.mk' H.toLieSubmodule : L →ₗ[R] _) ∈ relativeCochains R M H n := by
  refine ⟨?_, (LieSubmodule.mem_toSubmodule _).mpr <|
    (LieModule.mem_maxTrivSubmodule R H _ _).mpr fun y ↦ ?_⟩
  · rw [LieSubmodule.Quotient.coe_mk', ← Submodule.conormalPullback_apply]
    exact Submodule.conormalPullback_mem _ _
  rw [LieSubalgebra.coe_bracket_of_module, lie_compLinearMap_mk' y,
    (LieModule.mem_maxTrivSubmodule R H _ _).mp η.property y, zero_compLinearMap]

/-- Pullback along `L → L ⧸ H`, from `H`-invariant alternating maps on `L ⧸ H` to relative
cochains. -/
def relativeCochainsPullback (n : ℕ) :
    LieModule.maxTrivSubmodule R H ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) →ₗ[R]
      relativeCochains R M H n where
  toFun η := ⟨_, compLinearMap_mk'_mem_relativeCochains η⟩
  map_add' _ _ := Subtype.ext (AlternatingMap.ext fun _ ↦ by simp)
  map_smul' _ _ := Subtype.ext (AlternatingMap.ext fun _ ↦ by simp)

@[simp]
theorem coe_relativeCochainsPullback_apply {n : ℕ}
    (η : LieModule.maxTrivSubmodule R H ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M))
    (v : Fin n → L) :
    (relativeCochainsPullback R M H n η : L [⋀^Fin n]→ₗ[R] M) v =
      (η : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) fun i ↦ LieSubmodule.Quotient.mk (v i) :=
  (rfl)

theorem relativeCochainsPullback_injective (n : ℕ) :
    Function.Injective (relativeCochainsPullback R M H n) := fun _ _ h ↦
  Subtype.ext <| H.toLieSubmodule.toSubmodule.conormalPullback_injective <| by
    rw [Submodule.conormalPullback_apply, Submodule.conormalPullback_apply,
      ← LieSubmodule.Quotient.coe_mk']
    exact congrArg Subtype.val h

variable {R M H} in
/-- A relative cochain descends to an alternating map on `L ⧸ H`. -/
theorem exists_compLinearMap_mk'_eq {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ relativeCochains R M H n) :
    ∃ η : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M,
      η.compLinearMap (LieSubmodule.Quotient.mk' H.toLieSubmodule : L →ₗ[R] _) = ω := by
  rw [LieSubmodule.Quotient.coe_mk']
  exact Submodule.exists_compLinearMap_mkQ_eq hω.1

theorem relativeCochainsPullback_surjective (n : ℕ) :
    Function.Surjective (relativeCochainsPullback R M H n) := by
  rintro ⟨ω, hω⟩
  obtain ⟨η, rfl⟩ := exists_compLinearMap_mk'_eq hω
  refine ⟨⟨η, (LieModule.mem_maxTrivSubmodule R H _ _).mpr fun y ↦ ?_⟩, rfl⟩
  refine compLinearMap_injective _ (LieSubmodule.Quotient.surjective_mk' H.toLieSubmodule) ?_
  dsimp only
  rw [← lie_compLinearMap_mk', (mem_relativeCochains_iff.mp hω).2 y y.property, zero_compLinearMap]

/-- **Relative cochains are `Hom_H(⋀ⁿ(L/H), M)`**: pullback along `L → L ⧸ H` identifies the
`H`-invariant alternating maps on `L ⧸ H` with the relative cochains of `(L, H)`. -/
noncomputable def relativeCochainsEquiv (n : ℕ) :
    LieModule.maxTrivSubmodule R H ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M) ≃ₗ[R]
      relativeCochains R M H n :=
  LinearEquiv.ofBijective _
    ⟨relativeCochainsPullback_injective R M H n, relativeCochainsPullback_surjective R M H n⟩

@[simp]
theorem relativeCochainsEquiv_apply {n : ℕ}
    (η : LieModule.maxTrivSubmodule R H ((L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)) :
    relativeCochainsEquiv R M H n η = relativeCochainsPullback R M H n η :=
  (rfl)

/-- The alternating map on `L ⧸ H` attached to a relative cochain evaluates on classes by the
cochain. -/
@[simp]
theorem relativeCochainsEquiv_symm_apply_mk {n : ℕ} (ω : relativeCochains R M H n)
    (v : Fin n → L) :
    ((relativeCochainsEquiv R M H n).symm ω : (L ⧸ H.toLieSubmodule) [⋀^Fin n]→ₗ[R] M)
        (fun i ↦ LieSubmodule.Quotient.mk (v i)) = (ω : L [⋀^Fin n]→ₗ[R] M) v := by
  rw [← coe_relativeCochainsPullback_apply, ← relativeCochainsEquiv_apply,
    LinearEquiv.apply_symm_apply]

end Relative

/-! ### The relative complex of a pair `(𝔤, K)` -/

section Equivariant

variable (R M) {K : Type*} (Ad : K → L →ₗ⁅R⁆ L) (ρ : K → M →ₗ[R] M) (H : LieSubalgebra R L)

/-- The `K`-equivariant `(L, H)`-relative `n`-cochains, for a family of Lie algebra morphisms
`Ad k : L → L` and linear maps `ρ k : M → M` indexed by `k : K`: the relative cochains of `(L, H)`
with `ω (Ad k ∘ v) = ρ k (ω v)`. For a group `K` acting on `L` by Lie algebra automorphisms and on
`M` compatibly, when `H` is `Ad(K)`-stable, these are `Hom_K(⋀ⁿ(L/H), M)` with `H`-invariance
imposed, and when moreover `H` is the Lie algebra of a Lie group `K` acting on a `(L, K)`-module
`M`, they are the relative `n`-cochains of the pair `(L, K)`. -/
def equivariantRelativeCochains (n : ℕ) : Submodule R (L [⋀^Fin n]→ₗ[R] M) :=
  relativeCochains R M H n ⊓
    { carrier := {ω | ∀ (k : K) (v : Fin n → L), ω (fun i ↦ Ad k (v i)) = ρ k (ω v)}
      add_mem' {ω ω'} hω hω' k v := by simp [hω k v, hω' k v]
      zero_mem' _ _ := by simp
      smul_mem' c ω hω k v := by simp [hω k v] }

variable {R M Ad ρ H}

@[simp]
theorem mem_equivariantRelativeCochains_iff {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M} :
    ω ∈ equivariantRelativeCochains R M Ad ρ H n ↔
      ω ∈ relativeCochains R M H n ∧
        ∀ (k : K) (v : Fin n → L), ω (fun i ↦ Ad k (v i)) = ρ k (ω v) :=
  Iff.rfl

theorem equivariantRelativeCochains_le_relativeCochains (n : ℕ) :
    equivariantRelativeCochains R M Ad ρ H n ≤ relativeCochains R M H n :=
  inf_le_left

variable (R M Ad ρ H) in
/-- With no equivariance condition, the equivariant relative cochains are the relative
cochains. -/
@[simp]
theorem equivariantRelativeCochains_of_isEmpty [IsEmpty K] (n : ℕ) :
    equivariantRelativeCochains R M Ad ρ H n = relativeCochains R M H n :=
  inf_eq_left.mpr fun _ _ k ↦ isEmptyElim k

/-- **The differential preserves `K`-equivariant relative cochains**, when each `ρ k` intertwines
the action of `x` on `M` with that of `Ad k x`. -/
theorem d_mem_equivariantRelativeCochains (hρ : ∀ k x m, ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆) {n : ℕ}
    {ω : L [⋀^Fin n]→ₗ[R] M} (hω : ω ∈ equivariantRelativeCochains R M Ad ρ H n) :
    d R L M n ω ∈ equivariantRelativeCochains R M Ad ρ H (n + 1) := by
  refine ⟨d_mem_relativeCochains hω.1, fun k v ↦ ?_⟩
  have h : ω.compLinearMap (Ad k : L →ₗ[R] L) = (ρ k).compAlternatingMap ω := by
    ext w
    exact hω.2 k w
  simpa using congr($(compLinearMap_d_eq_compAlternatingMap_d (Ad k) (hρ k) h) v)

variable (R M Ad ρ H)

/-- The complex of `K`-equivariant `(L, H)`-relative cochains. When `K` is a group acting on `L`
by Lie algebra automorphisms, `H` is `Ad(K)`-stable and is the Lie algebra of a Lie group `K`, and
`M` is an `(L, K)`-module, this is the relative Chevalley–Eilenberg complex `C^•(L, K; M)` of the
pair `(L, K)`. -/
noncomputable abbrev equivariantRelativeCochainComplex
    (hρ : ∀ k x m, ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆) : CochainComplex (ModuleCat R) ℕ :=
  cochainSubcomplex (equivariantRelativeCochains R M Ad ρ H) fun _ _ ↦
    d_mem_equivariantRelativeCochains hρ

/-- The `n`-th cohomology of the complex of `K`-equivariant `(L, H)`-relative cochains. When `K`
is a group acting on `L` by Lie algebra automorphisms, `H` is `Ad(K)`-stable and is the Lie
algebra of a Lie group `K`, and `M` is an `(L, K)`-module, this is the relative Lie algebra
cohomology `H^n(L, K; M)` of the pair `(L, K)`. -/
noncomputable abbrev equivariantRelativeCohomology
    (hρ : ∀ k x m, ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆) (n : ℕ) : ModuleCat R :=
  (equivariantRelativeCochainComplex R M Ad ρ H hρ).homology n

end Equivariant

end TauCeti.LieModule.Cohomology
