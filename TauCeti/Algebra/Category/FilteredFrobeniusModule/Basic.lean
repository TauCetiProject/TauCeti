/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Filtered modules with divided Frobenius maps

Let `W` be a commutative ring with a ring endomorphism `σ` and an element `ϖ`. A *filtered
Frobenius module* over `(W, σ, ϖ)` is a `W`-module `M` with a decreasing, exhaustive and
separated filtration `(Fil^i M)_{i ∈ ℤ}` by submodules, together with `σ`-semilinear maps
`φ^i : Fil^i M → M`, the *divided Frobenius maps*, such that `φ^i x = ϖ • φ^(i + 1) x` for
`x ∈ Fil^(i + 1) M`. When `W = W(k)` is the ring of Witt vectors of a perfect field `k` of
characteristic `p`, `σ` is its Frobenius and `ϖ = p`, these are the filtered modules of
Fontaine and Laffaille: on `Fil^i M` the map `φ^i` plays the role of `p ^ (-i) φ`, which
need not make sense on `M` itself. Fontaine and Laffaille work with a general base
`(A, τ, π)`, which is why the element `ϖ` is not required to be `p`.

The finite-length objects that are *generating*, in the sense that the images of the `φ^i`
span `M`, form Fontaine and Laffaille's torsion category `MF_tor`, and those with filtration
support `[a, b]`, that is `Fil^a M = M` and `Fil^(b + 1) M = 0`, form `MF_tor^[a,b]`. Over
`W(k)` with `p > 2` the subcategory with support `[0, 1]` classifies finite flat group schemes
over `W(k)`, and the subcategories of small width are the source of the Fontaine–Laffaille
realization functors. Here neither generation nor finiteness is part of the structure, so
`TauCeti.FilteredFrobeniusModule σ ϖ` is the enlarged category of all filtered modules; the
torsion categories are its full subcategories cut out by finite length of the underlying module
together with the predicates below.

The divided Frobenius maps satisfy `φ^i x = ϖ ^ n • φ^(i + n) x` for `x ∈ Fil^(i + n) M`. So
on an object with support `[a, b]` the maps `φ^i` with `i < a` are determined by `φ^a`, those
with `i > b` vanish, and generation only involves `φ^a, …, φ^b`.

## Main definitions

* `TauCeti.FilteredFrobeniusModule σ ϖ`: the category of filtered Frobenius modules over
  `(W, σ, ϖ)`, whose morphisms are the linear maps preserving the filtrations and commuting
  with every divided Frobenius map. It is preadditive.
* `TauCeti.FilteredFrobeniusModule.homAddSubgroup M N`: the underlying linear maps of the
  morphisms `M ⟶ N`, as an additive subgroup; the preadditive structure is built from it.
* `TauCeti.FilteredFrobeniusModule.isoMk`: an isomorphism from a linear equivalence carrying
  each filtration step onto the corresponding step and commuting with the divided Frobenius
  maps.
* `TauCeti.FilteredFrobeniusModule.IsSupportedIn M a b`: the filtration of `M` has support
  `[a, b]`.
* `TauCeti.FilteredFrobeniusModule.IsGenerating M`: the images of the divided Frobenius maps of
  `M` span `M`.

## Main results

* `TauCeti.FilteredFrobeniusModule.phi_eq_pow_smul`: `φ^i x = ϖ ^ n • φ^(i + n) x` on
  `Fil^(i + n) M`.
* `TauCeti.FilteredFrobeniusModule.isIso_iff_bijective_and_map_fil_eq`: a morphism is an
  isomorphism iff it is bijective and strict, that is it maps each filtration step onto the
  corresponding step.
  Bijectivity alone does not suffice.
* `TauCeti.FilteredFrobeniusModule.exists_isSupportedIn`: a filtered Frobenius module whose
  underlying module has finite length has a filtration support `[a, b]`.
* `TauCeti.FilteredFrobeniusModule.IsSupportedIn.le`: a nonzero module supported in `[a, b]`
  has `a ≤ b`.
* `TauCeti.FilteredFrobeniusModule.isGenerating_iff_of_isSupportedIn`: on an object supported
  in `[a, b]`, generation only involves `φ^a, …, φ^b`.
* `TauCeti.FilteredFrobeniusModule.isGenerating_iff_iSup_range`: if `σ` is surjective,
  generation says that `M` is the sum of the images `φ^i (Fil^i M)`.
* `TauCeti.FilteredFrobeniusModule.IsGenerating.of_surjective`: generation passes to the target
  of a surjective morphism.

## References

* J.-M. Fontaine and G. Laffaille, *Construction de représentations p-adiques*, Ann. Sci. École
  Norm. Sup. (4) 15 (1982), §§0.4, 1.2, 1.5 and 3.2.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti

variable {W : Type u} [CommRing W]

/-- A filtered Frobenius module over a commutative ring `W` with a ring endomorphism `σ` and an
element `ϖ`: a `W`-module with a decreasing, exhaustive and separated filtration indexed by `ℤ`
and `σ`-semilinear divided Frobenius maps `φ^i : Fil^i M → M` with `φ^i = ϖ • φ^(i + 1)` on
`Fil^(i + 1) M`. -/
structure FilteredFrobeniusModule (σ : W →+* W) (ϖ : W) where
  /-- The underlying `W`-module. -/
  toModuleCat : ModuleCat.{v} W
  /-- The filtration `Fil^i M`. -/
  fil : ℤ → Submodule W toModuleCat
  /-- The filtration is decreasing. -/
  fil_antitone : Antitone fil
  /-- The filtration is exhaustive. -/
  iSup_fil : ⨆ i, fil i = ⊤
  /-- The filtration is separated. -/
  iInf_fil : ⨅ i, fil i = ⊥
  /-- The divided Frobenius map `φ^i : Fil^i M → M`. -/
  phi (i : ℤ) : fil i →ₛₗ[σ] toModuleCat
  /-- On `Fil^(i + 1) M`, the divided Frobenius map `φ^i` is `ϖ • φ^(i + 1)`. -/
  phi_succ (i : ℤ) (x : toModuleCat) (hx : x ∈ fil (i + 1)) :
    phi i ⟨x, fil_antitone (lt_add_one i).le hx⟩ = ϖ • phi (i + 1) ⟨x, hx⟩

namespace FilteredFrobeniusModule

variable {σ : W →+* W} {ϖ : W}

instance : CoeSort (FilteredFrobeniusModule.{v} σ ϖ) (Type v) := ⟨fun M => M.toModuleCat⟩

section Phi

variable (M : FilteredFrobeniusModule.{v} σ ϖ)

/-- The divided Frobenius maps of equal index agree: `φ^i x = φ^j x` when `i = j`, for the two
membership proofs `x ∈ Fil^i M` and `x ∈ Fil^j M`. -/
theorem phi_congr {i j : ℤ} (h : i = j) {x : M} (hi : x ∈ M.fil i) (hj : x ∈ M.fil j) :
    M.phi i ⟨x, hi⟩ = M.phi j ⟨x, hj⟩ := by
  subst h
  rfl

/-- `φ^i x = ϖ ^ n • φ^(i + n) x` for `x ∈ Fil^(i + n) M`. -/
theorem phi_eq_pow_smul (i : ℤ) (n : ℕ) {x : M} (hx : x ∈ M.fil (i + n)) :
    M.phi i ⟨x, M.fil_antitone (by omega) hx⟩ = ϖ ^ n • M.phi (i + n) ⟨x, hx⟩ := by
  induction n with
  | zero => simpa using M.phi_congr (by simp) _ hx
  | succ n ih =>
    have hx' : x ∈ M.fil (i + n + 1) := by rwa [Nat.cast_succ, ← add_assoc] at hx
    rw [ih (M.fil_antitone (by omega) hx), M.phi_succ (i + n) x hx', pow_succ, mul_smul,
      M.phi_congr (by push_cast; ring) hx' hx]

/-- `φ^i x = ϖ ^ (j - i) • φ^j x` for `i ≤ j` and `x ∈ Fil^j M`. -/
theorem phi_eq_pow_toNat_smul {i j : ℤ} (hij : i ≤ j) {x : M} (hx : x ∈ M.fil j) :
    M.phi i ⟨x, M.fil_antitone hij hx⟩ = ϖ ^ (j - i).toNat • M.phi j ⟨x, hx⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = i + n := ⟨(j - i).toNat, by omega⟩
  rw [show (i + n - i).toNat = n by omega]
  exact M.phi_eq_pow_smul i n hx

/-- The image of `φ^i` lies in the span of the image of `φ^j` for `i ≤ j`, on `Fil^j M`. -/
theorem phi_mem_span_range {i j : ℤ} (hij : i ≤ j) {x : M} (hx : x ∈ M.fil j) :
    M.phi i ⟨x, M.fil_antitone hij hx⟩ ∈ Submodule.span W (Set.range (M.phi j)) := by
  rw [M.phi_eq_pow_toNat_smul hij hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Phi

/-! ### Morphisms -/

/-- A morphism of filtered Frobenius modules: a linear map preserving the filtrations and
commuting with every divided Frobenius map. -/
@[ext]
structure Hom (M N : FilteredFrobeniusModule.{v} σ ϖ) where
  /-- The underlying linear map. -/
  hom : M →ₗ[W] N
  /-- The linear map preserves the filtrations. -/
  map_fil (i : ℤ) : M.fil i ≤ (N.fil i).comap hom
  /-- The linear map commutes with the divided Frobenius maps. -/
  hom_phi (i : ℤ) (x : M) (hx : x ∈ M.fil i) :
    hom (M.phi i ⟨x, hx⟩) = N.phi i ⟨hom x, map_fil i hx⟩

instance {M N : FilteredFrobeniusModule.{v} σ ϖ} : FunLike (Hom M N) M N where
  coe f := f.hom
  coe_injective _ _ h := Hom.ext (DFunLike.coe_injective h)

instance : Category (FilteredFrobeniusModule.{v} σ ϖ) where
  Hom := Hom
  id M := ⟨LinearMap.id, fun _ _ hx => hx, fun _ _ _ => rfl⟩
  comp f g := ⟨g.hom.comp f.hom, fun i _ hx => g.map_fil i (f.map_fil i hx),
    fun i x hx => by simp only [LinearMap.comp_apply, f.hom_phi, g.hom_phi]⟩

instance : ConcreteCategory (FilteredFrobeniusModule.{v} σ ϖ) Hom where
  hom f := f
  ofHom f := f

variable {M N P : FilteredFrobeniusModule.{v} σ ϖ}

@[simp]
theorem Hom.coe_hom_apply (f : M ⟶ N) (x : M) : f x = f.hom x := (rfl)

/-- A morphism maps `Fil^i M` into `Fil^i N`. -/
theorem Hom.hom_mem_fil (f : M ⟶ N) {i : ℤ} {x : M} (hx : x ∈ M.fil i) : f.hom x ∈ N.fil i :=
  f.map_fil i hx

/-- Morphisms of filtered Frobenius modules are determined by their underlying linear maps. -/
@[ext]
theorem hom_ext {f g : M ⟶ N} (h : f.hom = g.hom) : f = g := Hom.ext h

theorem hom_injective : Function.Injective (Hom.hom : (M ⟶ N) → (M →ₗ[W] N)) :=
  fun _ _ => hom_ext

@[simp]
theorem hom_id (M : FilteredFrobeniusModule.{v} σ ϖ) : (𝟙 M : M ⟶ M).hom = LinearMap.id := (rfl)

@[simp]
theorem hom_comp (f : M ⟶ N) (g : N ⟶ P) : (f ≫ g).hom = g.hom.comp f.hom := (rfl)

/-- The forgetful functor to `W`-modules. -/
instance : HasForget₂ (FilteredFrobeniusModule.{v} σ ϖ) (ModuleCat.{v} W) where
  forget₂ :=
    { obj M := M.toModuleCat
      map f := ModuleCat.ofHom f.hom }

@[simp]
theorem forget₂_obj (M : FilteredFrobeniusModule.{v} σ ϖ) :
    (forget₂ (FilteredFrobeniusModule σ ϖ) (ModuleCat W)).obj M = M.toModuleCat := (rfl)

@[simp]
theorem forget₂_map (f : M ⟶ N) :
    ((forget₂ (FilteredFrobeniusModule σ ϖ) (ModuleCat W)).map f).hom = f.hom := (rfl)

instance : (forget₂ (FilteredFrobeniusModule.{v} σ ϖ) (ModuleCat.{v} W)).Faithful where
  map_injective h := hom_ext (congrArg ModuleCat.Hom.hom h)

/-! ### Isomorphisms -/

/-- A linear equivalence carrying each filtration step onto the corresponding step and
commuting with the divided Frobenius maps is an isomorphism of filtered Frobenius modules. -/
def isoMk (e : M ≃ₗ[W] N) (he : ∀ i, (M.fil i).map e.toLinearMap = N.fil i)
    (hphi : ∀ i (x : M) (hx : x ∈ M.fil i),
      e (M.phi i ⟨x, hx⟩) = N.phi i ⟨e x, he i ▸ Submodule.mem_map_of_mem hx⟩) :
    M ≅ N where
  hom := ⟨e.toLinearMap, fun i _ hx => he i ▸ Submodule.mem_map_of_mem hx, hphi⟩
  inv :=
    { hom := e.symm.toLinearMap
      map_fil i y hy := by
        rw [← he i] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simpa using hx
      hom_phi i y hy := by
        rw [← he i] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        apply e.injective
        simp [hphi i x hx] }
  hom_inv_id := hom_ext (LinearMap.ext e.symm_apply_apply)
  inv_hom_id := hom_ext (LinearMap.ext e.apply_symm_apply)

@[simp]
theorem isoMk_hom_hom (e : M ≃ₗ[W] N) (he) (hphi) : (isoMk e he hphi).hom.hom = e.toLinearMap :=
  (rfl)

@[simp]
theorem isoMk_inv_hom (e : M ≃ₗ[W] N) (he) (hphi) :
    (isoMk e he hphi).inv.hom = e.symm.toLinearMap := (rfl)

/-- An isomorphism maps each filtration step onto the corresponding step. -/
theorem map_fil_hom_eq (e : M ≅ N) (i : ℤ) : (M.fil i).map e.hom.hom = N.fil i := by
  refine le_antisymm (Submodule.map_le_iff_le_comap.2 (e.hom.map_fil i)) fun y hy => ?_
  refine ⟨e.inv.hom y, e.inv.map_fil i hy, ?_⟩
  simpa only [hom_comp, hom_id, LinearMap.comp_apply, LinearMap.id_apply] using
    congrArg (fun f : N ⟶ N => f.hom y) e.inv_hom_id

/-- A morphism of filtered Frobenius modules is an isomorphism iff its underlying linear map
is bijective and *strict*: it maps each filtration step onto the corresponding step. -/
theorem isIso_iff_bijective_and_map_fil_eq (f : M ⟶ N) :
    IsIso f ↔ Function.Bijective f.hom ∧ ∀ i, (M.fil i).map f.hom = N.fil i := by
  refine ⟨fun _ => ⟨ConcreteCategory.bijective_of_isIso f, map_fil_hom_eq (asIso f)⟩,
    fun ⟨hf, hfil⟩ => ?_⟩
  exact (isoMk (LinearEquiv.ofBijective f.hom hf) hfil f.hom_phi).isIso_hom

/-! ### The preadditive structure -/

/-- The underlying linear maps of the morphisms `M ⟶ N` form an additive subgroup: these are
the linear maps preserving the filtrations and commuting with the divided Frobenius maps. -/
def homAddSubgroup (M N : FilteredFrobeniusModule.{v} σ ϖ) :
    AddSubgroup (M →ₗ[W] N) where
  carrier := {g | ∀ i (x : M) (hx : x ∈ M.fil i), ∃ hgx : g x ∈ N.fil i,
    g (M.phi i ⟨x, hx⟩) = N.phi i ⟨g x, hgx⟩}
  zero_mem' {i} _ _ := ⟨zero_mem _, (map_zero (N.phi i)).symm⟩
  add_mem' {f g} hf hg i x hx := by
    obtain ⟨hf₁, hf₂⟩ := hf i x hx
    obtain ⟨hg₁, hg₂⟩ := hg i x hx
    refine ⟨add_mem hf₁ hg₁, ?_⟩
    rw [LinearMap.add_apply, hf₂, hg₂, ← map_add]
    exact congrArg _ (Subtype.ext (by simp))
  neg_mem' {f} hf i x hx := by
    obtain ⟨hf₁, hf₂⟩ := hf i x hx
    refine ⟨neg_mem hf₁, ?_⟩
    rw [LinearMap.neg_apply, hf₂, ← map_neg]
    exact congrArg _ (Subtype.ext (by simp))

/-- A linear map lies in `homAddSubgroup M N` iff it maps each `Fil^i M` into `Fil^i N` and
commutes with `φ^i`. -/
theorem mem_homAddSubgroup {g : M →ₗ[W] N} :
    g ∈ homAddSubgroup M N ↔ ∀ i (x : M) (hx : x ∈ M.fil i), ∃ hgx : g x ∈ N.fil i,
      g (M.phi i ⟨x, hx⟩) = N.phi i ⟨g x, hgx⟩ := Iff.rfl

/-- The underlying linear map of a morphism lies in `homAddSubgroup M N`. -/
theorem Hom.hom_mem_homAddSubgroup (f : M ⟶ N) : f.hom ∈ homAddSubgroup M N :=
  fun i x hx => ⟨f.map_fil i hx, f.hom_phi i x hx⟩

/-- The morphism with a given underlying linear map in `homAddSubgroup M N`. -/
def homOfMem {g : M →ₗ[W] N} (hg : g ∈ homAddSubgroup M N) : M ⟶ N :=
  ⟨g, fun i _ hx => (mem_homAddSubgroup.1 hg i _ hx).1,
    fun i x hx => (mem_homAddSubgroup.1 hg i x hx).2⟩

@[simp]
theorem hom_homOfMem {g : M →ₗ[W] N} (hg : g ∈ homAddSubgroup M N) : (homOfMem hg).hom = g :=
  (rfl)

instance : Zero (M ⟶ N) := ⟨homOfMem (zero_mem _)⟩

instance : Add (M ⟶ N) :=
  ⟨fun f g => homOfMem (add_mem f.hom_mem_homAddSubgroup g.hom_mem_homAddSubgroup)⟩

instance : Neg (M ⟶ N) := ⟨fun f => homOfMem (neg_mem f.hom_mem_homAddSubgroup)⟩

instance : Sub (M ⟶ N) :=
  ⟨fun f g => homOfMem (sub_mem f.hom_mem_homAddSubgroup g.hom_mem_homAddSubgroup)⟩

instance : SMul ℕ (M ⟶ N) := ⟨fun n f => homOfMem (nsmul_mem f.hom_mem_homAddSubgroup n)⟩

instance : SMul ℤ (M ⟶ N) := ⟨fun n f => homOfMem (zsmul_mem f.hom_mem_homAddSubgroup n)⟩

@[simp] theorem hom_zero : (0 : M ⟶ N).hom = 0 := (rfl)

@[simp] theorem hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := (rfl)

@[simp] theorem hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := (rfl)

@[simp] theorem hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := (rfl)

@[simp] theorem hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := (rfl)

@[simp] theorem hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := (rfl)

instance : AddCommGroup (M ⟶ N) :=
  Function.Injective.addCommGroup Hom.hom hom_injective hom_zero hom_add hom_neg hom_sub
    (fun f n => hom_nsmul n f) (fun f n => hom_zsmul n f)

instance : Preadditive (FilteredFrobeniusModule.{v} σ ϖ) where
  add_comp _ _ _ _ _ _ := hom_ext (by simp [LinearMap.comp_add])
  comp_add _ _ _ _ _ _ := hom_ext (by simp [LinearMap.add_comp])

instance : (forget₂ (FilteredFrobeniusModule.{v} σ ϖ) (ModuleCat.{v} W)).Additive where
  map_add := ModuleCat.hom_ext (by simp)

/-! ### Filtration support -/

/-- The filtration of `M` has support in `[a, b]`: `Fil^a M = M` and `Fil^(b + 1) M = 0`.
These are the filtration jumps of Fontaine–Laffaille's categories `MF^[a,b]`. -/
def IsSupportedIn (M : FilteredFrobeniusModule.{v} σ ϖ) (a b : ℤ) : Prop :=
  M.fil a = ⊤ ∧ M.fil (b + 1) = ⊥

theorem isSupportedIn_iff (M : FilteredFrobeniusModule.{v} σ ϖ) (a b : ℤ) :
    M.IsSupportedIn a b ↔ M.fil a = ⊤ ∧ M.fil (b + 1) = ⊥ := Iff.rfl

namespace IsSupportedIn

variable {a b : ℤ}

theorem fil_eq_top (h : M.IsSupportedIn a b) {i : ℤ} (hi : i ≤ a) : M.fil i = ⊤ :=
  top_le_iff.1 (h.1 ▸ M.fil_antitone hi)

theorem fil_eq_bot (h : M.IsSupportedIn a b) {i : ℤ} (hi : b < i) : M.fil i = ⊥ :=
  le_bot_iff.1 (h.2 ▸ M.fil_antitone (by omega))

theorem mono (h : M.IsSupportedIn a b) {a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    M.IsSupportedIn a' b' :=
  ⟨h.fil_eq_top ha, h.fil_eq_bot (by omega)⟩

/-- A nonzero filtered Frobenius module cannot be supported in a reversed interval. -/
theorem le [Nontrivial M] (h : M.IsSupportedIn a b) : a ≤ b := by
  by_contra hab
  have : (⊤ : Submodule W M) = ⊥ := (h.fil_eq_top le_rfl).symm.trans (h.fil_eq_bot (by omega))
  exact top_ne_bot this

/-- Filtration support is invariant under isomorphism. -/
theorem of_iso (h : M.IsSupportedIn a b) (e : M ≅ N) : N.IsSupportedIn a b := by
  refine ⟨?_, ?_⟩
  · rw [← map_fil_hom_eq e, h.1, Submodule.map_top, LinearMap.range_eq_top]
    exact (ConcreteCategory.bijective_of_isIso e.hom).surjective
  · rw [← map_fil_hom_eq e, h.2, Submodule.map_bot]

end IsSupportedIn

/-- The zero module is supported in every interval, including reversed ones. -/
theorem isSupportedIn_of_subsingleton [Subsingleton M] (a b : ℤ) : M.IsSupportedIn a b :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Over a Noetherian module the exhaustive filtration reaches the whole module. -/
theorem exists_fil_eq_top [IsNoetherian W M] : ∃ a, M.fil a = ⊤ := by
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ :=
    (wellFounded_gt (α := Submodule W M)).has_min (Set.range M.fil) ⟨_, 0, rfl⟩
  refine ⟨a, top_le_iff.1 (M.iSup_fil ▸ iSup_le fun i => ?_)⟩
  have hle : M.fil a ≤ M.fil (min a i) := M.fil_antitone (min_le_left a i)
  exact (eq_of_le_of_not_lt hle (ha _ ⟨_, rfl⟩)).symm ▸ M.fil_antitone (min_le_right a i)

/-- Over an Artinian module the separated filtration reaches zero. -/
theorem exists_fil_eq_bot [IsArtinian W M] : ∃ b, M.fil b = ⊥ := by
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ :=
    (wellFounded_lt (α := Submodule W M)).has_min (Set.range M.fil) ⟨_, 0, rfl⟩
  refine ⟨b, le_bot_iff.1 (M.iInf_fil ▸ le_iInf fun i => ?_)⟩
  have hle : M.fil (max b i) ≤ M.fil b := M.fil_antitone (le_max_left b i)
  exact (eq_of_le_of_not_lt hle (hb _ ⟨_, rfl⟩)) ▸ M.fil_antitone (le_max_right b i)

/-- A filtered Frobenius module of finite length has a filtration support `[a, b]`. -/
theorem exists_isSupportedIn [IsNoetherian W M] [IsArtinian W M] :
    ∃ a b, M.IsSupportedIn a b := by
  obtain ⟨a, ha⟩ := M.exists_fil_eq_top
  obtain ⟨b, hb⟩ := M.exists_fil_eq_bot
  exact ⟨a, b - 1, ha, by simpa using hb⟩

/-! ### Generation -/

/-- The divided Frobenius maps of `M` are *generating*: their images span `M` over `W`. When
`σ` is surjective this says that `M` is the sum of the submodules `φ^i (Fil^i M)`. -/
def IsGenerating (M : FilteredFrobeniusModule.{v} σ ϖ) : Prop :=
  Submodule.span W (⋃ i, Set.range (M.phi i)) = ⊤

theorem isGenerating_iff (M : FilteredFrobeniusModule.{v} σ ϖ) :
    M.IsGenerating ↔ Submodule.span W (⋃ i, Set.range (M.phi i)) = ⊤ := Iff.rfl

theorem isGenerating_iff_iSup_span (M : FilteredFrobeniusModule.{v} σ ϖ) :
    M.IsGenerating ↔ ⨆ i, Submodule.span W (Set.range (M.phi i)) = ⊤ := by
  rw [isGenerating_iff, Submodule.span_iUnion]

/-- If `σ` is surjective, the divided Frobenius maps are generating iff `M` is the sum of the
images `φ^i (Fil^i M)`. -/
theorem isGenerating_iff_iSup_range [RingHomSurjective σ] (M : FilteredFrobeniusModule.{v} σ ϖ) :
    M.IsGenerating ↔ ⨆ i, LinearMap.range (M.phi i) = ⊤ := by
  simp only [isGenerating_iff_iSup_span, ← LinearMap.coe_range, Submodule.span_eq]

/-- On an object supported in `[a, b]`, the divided Frobenius maps are generating iff
`φ^a, …, φ^b` are: below `a` they are multiples of `φ^a`, and above `b` they vanish. -/
theorem isGenerating_iff_of_isSupportedIn {a b : ℤ} (h : M.IsSupportedIn a b) :
    M.IsGenerating ↔ ⨆ i ∈ Set.Icc a b, Submodule.span W (Set.range (M.phi i)) = ⊤ := by
  rw [isGenerating_iff_iSup_span]
  congr! 1
  refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun i _ => le_iSup_of_le i le_rfl)
  rw [Submodule.span_le]
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  by_cases hx0 : x = 0
  · subst hx0
    exact (map_zero (M.phi i)).symm ▸ zero_mem _
  have hib : i ≤ b := by
    by_contra hbi
    exact hx0 (by simpa [h.fil_eq_bot (not_le.1 hbi)] using hx)
  rcases lt_or_ge i a with hia | hai
  · have hxa : x ∈ M.fil a := h.1 ▸ Submodule.mem_top
    have : Nontrivial M := nontrivial_of_ne x 0 hx0
    exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem
      (Set.mem_Icc.2 ⟨le_rfl, h.le⟩) (M.phi_mem_span_range hia.le hxa))
  · exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem
      (Set.mem_Icc.2 ⟨hai, hib⟩) (Submodule.subset_span ⟨_, rfl⟩))

/-- A morphism maps the span of the images of the divided Frobenius maps of its source into the
corresponding span for its target. -/
theorem Hom.map_span_range_phi_le (f : M ⟶ N) :
    (Submodule.span W (⋃ i, Set.range (M.phi i))).map f.hom ≤
      Submodule.span W (⋃ i, Set.range (N.phi i)) := by
  rw [Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := Set.mem_iUnion.1 hy
  exact Set.mem_iUnion.2 ⟨i, _, (f.hom_phi i x hx).symm⟩

/-- Generation passes to the target of a surjective morphism. -/
theorem IsGenerating.of_surjective (h : M.IsGenerating) (f : M ⟶ N)
    (hf : Function.Surjective f.hom) : N.IsGenerating := by
  rw [isGenerating_iff] at h ⊢
  refine top_le_iff.1 ?_
  rw [← LinearMap.range_eq_top.2 hf, LinearMap.range_eq_map, ← h]
  exact f.map_span_range_phi_le

/-- Generation is invariant under isomorphism. -/
theorem IsGenerating.of_iso (h : M.IsGenerating) (e : M ≅ N) : N.IsGenerating :=
  h.of_surjective e.hom (ConcreteCategory.bijective_of_isIso e.hom).surjective

end FilteredFrobeniusModule

end TauCeti
