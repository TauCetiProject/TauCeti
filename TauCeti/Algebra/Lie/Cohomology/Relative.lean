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
public import TauCeti.RepresentationTheory.LieHom

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

Let a group `K` act on `𝔤` by Lie algebra automorphisms `Ad` and on `M` compatibly,
`k • ⁅x, m⁆ = ⁅Ad k x, k • m⁆`, and let `𝔨` be a subalgebra. The `K`-equivariant
`(𝔤, 𝔨)`-relative cochains form a subcomplex, because the differential is natural
(`cochainMap_d`). When `𝔨` is `Ad(K)`-stable, they are `Hom_K(⋀ⁿ(𝔤/𝔨), M)` with `𝔨`-invariance
imposed. When moreover `K` is a Lie group with Lie algebra `𝔨` and `M` is a `(𝔤, K)`-module,
`K`-equivariance implies `𝔨`-invariance, and this is the relative complex `C^•(𝔤, K; M)` of the
pair `(𝔤, K)`. An abstract group carries no Lie algebra to differentiate, so here `𝔨` is a
separate datum and the `𝔨`-invariance is imposed. For `K` disconnected, as for `O(2)` inside
`GL₂(ℝ)`, the `K`-equivariance cuts out more than the `𝔨`-invariance does.

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

## Main results

* `TauCeti.LieModule.Cohomology.d_mem_relativeCochains`: the differential preserves relative
  cochains.
* `TauCeti.LieModule.Cohomology.d_mem_equivariantRelativeCochains`: the differential preserves
  `K`-equivariant relative cochains.
* `TauCeti.LieModule.Cohomology.relativeCochains_bot`: relative to the zero subalgebra, every
  cochain is relative.

## References

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

variable (R M) {K : Type*} [Group K] (Ad : Representation R K L) (ρ : Representation R K M)
  (H : LieSubalgebra R L)

/-- The `K`-equivariant `(L, H)`-relative `n`-cochains, for a group `K` acting on `L` through
`Ad` and on `M` through `ρ`: the relative cochains of `(L, H)` with `ω (Ad k ∘ v) = ρ k (ω v)`.
When `H` is `Ad(K)`-stable, these are `Hom_K(⋀ⁿ(L/H), M)` with `H`-invariance imposed, and when
moreover `H` is the Lie algebra of a Lie group `K` acting on a `(L, K)`-module `M`, they are the
relative `n`-cochains of the pair `(L, K)`. -/
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

/-- **The differential preserves `K`-equivariant relative cochains**, when `K` acts on `L` by
Lie algebra automorphisms and on `M` compatibly. -/
theorem d_mem_equivariantRelativeCochains (hAd : ∀ k x y, Ad k ⁅x, y⁆ = ⁅Ad k x, Ad k y⁆)
    (hρ : ∀ k x m, ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆) {n : ℕ} {ω : L [⋀^Fin n]→ₗ[R] M}
    (hω : ω ∈ equivariantRelativeCochains R M Ad ρ H n) :
    d R L M n ω ∈ equivariantRelativeCochains R M Ad ρ H (n + 1) := by
  refine ⟨d_mem_relativeCochains hω.1, fun k v ↦ ?_⟩
  -- `ω` is fixed by pullback along `Ad k` and pushforward along `ρ k⁻¹`, which commute with `d`.
  have hg : ∀ x m, ρ k⁻¹ ⁅Ad.toLieHom hAd k x, m⁆ = ⁅x, ρ k⁻¹ m⁆ := fun x m ↦ by
    rw [hρ, Representation.toLieHom_apply, Representation.inv_self_apply]
  have hfix : cochainMap (ρ k⁻¹) (Ad.toLieHom hAd k) n ω = ω := by
    ext w
    simp only [cochainMap_apply, Representation.toLieHom_apply, hω.2 k w,
      Representation.inv_self_apply]
  have h := congr($((cochainMap_d _ _ hg n ω).symm) v)
  rw [hfix] at h
  simp only [cochainMap_apply] at h
  rw [h]
  simp only [Representation.toLieHom_apply, Representation.self_inv_apply]

variable (R M Ad ρ H)

/-- The complex of `K`-equivariant `(L, H)`-relative cochains. When `H` is `Ad(K)`-stable and is
the Lie algebra of a Lie group `K`, and `M` is an `(L, K)`-module, this is the relative
Chevalley–Eilenberg complex `C^•(L, K; M)` of the pair `(L, K)`. -/
noncomputable abbrev equivariantRelativeCochainComplex
    (hAd : ∀ k x y, Ad k ⁅x, y⁆ = ⁅Ad k x, Ad k y⁆)
    (hρ : ∀ k x m, ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆) : CochainComplex (ModuleCat R) ℕ :=
  cochainSubcomplex (equivariantRelativeCochains R M Ad ρ H) fun _ _ ↦
    d_mem_equivariantRelativeCochains hAd hρ

/-- The `n`-th cohomology of the complex of `K`-equivariant `(L, H)`-relative cochains. When `H`
is `Ad(K)`-stable and is the Lie algebra of a Lie group `K`, and `M` is an `(L, K)`-module, this
is the relative Lie algebra cohomology `H^n(L, K; M)` of the pair `(L, K)`. -/
noncomputable abbrev equivariantRelativeCohomology
    (hAd : ∀ k x y, Ad k ⁅x, y⁆ = ⁅Ad k x, Ad k y⁆)
    (hρ : ∀ k x m, ρ k ⁅x, m⁆ = ⁅Ad k x, ρ k m⁆) (n : ℕ) : ModuleCat R :=
  (equivariantRelativeCochainComplex R M Ad ρ H hAd hρ).homology n

end Equivariant

end TauCeti.LieModule.Cohomology
