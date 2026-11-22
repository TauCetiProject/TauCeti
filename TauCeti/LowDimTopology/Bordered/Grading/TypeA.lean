/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Group.List
public import TauCeti.LowDimTopology.Bordered.Grading.Basic
public import TauCeti.LowDimTopology.Bordered.TypeA.Homotopy
import Mathlib.Tactic.Group

/-!
# Gradings of type `A` modules and of their box tensor products

The bordered algebras of Lipshitz, Ozsváth and Thurston are graded by a nonabelian group `G` with
a distinguished central element `λ`, and their modules are graded by `G`-sets. This file grades
the `A∞` right modules of `TauCeti.LowDimTopology.Bordered.TypeA.Basic`, the type `A` modules, and
shows that their box tensor products with graded type `D` structures are graded by the balanced
product of the two grading sets, with differential of degree `λ⁻¹`. It extends the gradings of
`TauCeti.LowDimTopology.Bordered.Grading.Basic`, which treat differential modules, to modules with
higher operations.

As there, the algebra `A` is graded by a family of submodules `Ag : G → Submodule R A`, a module
`M` by a family `Mg : S → Submodule R M` over a `G`-set `S` on which the right action is written
through inverses, `s · g = g⁻¹ • s`, and the central element `l` is the degree of the
differentials, `λ⁻¹` in the bordered algebras.

* **Graded `A∞` modules.** An `A∞` right module is graded
  (`TauCeti.UngradedAInfinityRightModule.IsGraded`) when its operation `m_{n+1}` has degree
  `λ^{n-1} = l^{1-n}`: for `m` of degree `s` and `aᵢ` of degree `gᵢ`,
  `m_{n+1}(m, a₁, …, aₙ)` has degree `s · l^{1-n} g₁ ⋯ gₙ`. So `m₁` has degree `l` and `m₂`
  is the graded right action. A differential module is graded in this sense exactly when its
  differential has degree `l` and its action is graded
  (`TauCeti.IsUngradedDGRightModule.isGraded_toUngradedAInfinityRightModule_iff`); in particular
  a graded differential algebra is a graded `A∞` module over itself
  (`TauCeti.IsUngradedDGAlgebra.isGraded_toUngradedAInfinityRightModule`).
* **Box tensor products.** The operations of the matrix module of a graded `A∞` module along
  matrices homogeneous of degree `l` raise the degree in the balanced product `S ×_G T` by `l`,
  whatever their arity: the `n` coefficients contribute `l^n` and the operation `l^{1-n}`
  (`TauCeti.UngradedAInfinityRightModule.IsGraded.matrixAct_mem_boxGradedPart`). Hence the box
  tensor differential `∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))` has degree `l`
  (`TauCeti.TypeDStructure.typeABoxDifferential_mem_boxGradedPart`). No boundedness hypothesis
  is needed, since an infinite sum is `0` by the convention of
  `TauCeti.UngradedAInfinityRightModule.twistedDifferential`. A morphism of type `D` structures
  homogeneous of central degree `c` induces a map of box tensor products of degree `c`
  (`TauCeti.TypeDStructure.typeABoxMap_mem_boxGradedPart`). For morphisms of degrees `c` and
  `c'`, the construction `TauCeti.TypeDStructure.typeABoxCompHomotopy` has degree `l⁻¹ c c'`
  (`TauCeti.TypeDStructure.typeABoxCompHomotopy_mem_boxGradedPart`), one `l` below the degree of
  the composite. Over a ring of characteristic two, for homomorphisms and a bounded module or
  bounded type `D` structures, it is the homotopy comparing the composite of the induced maps with
  the map of the composite morphism, and this degree is the one its homotopy equation requires.
* **Morphisms and homotopies of type `A` modules.** A morphism `f` of `A∞` modules graded over the
  same `G`-set is homogeneous of degree `c`
  (`TauCeti.UngradedAInfinityRightModuleHom.IsHomogeneous`) when `f_{n+1}` has degree
  `c λ^n = c l^{-n}`, so that `f₁` has degree `c`. Strict morphisms of graded modules, in
  particular identities, are homogeneous of degree `1`, sums of morphisms of degree `c` have
  degree `c`, and composites of morphisms of degrees `c` and `c'` have degree `c c'`
  (`TauCeti.UngradedAInfinityRightModuleHom.IsHomogeneous.comp`). A homotopy between morphisms of
  degree `c` is homogeneous (`TauCeti.UngradedAInfinityRightModuleHom.Homotopy.IsHomogeneous`)
  when `h_{n+1}` has degree `l⁻¹ c λ^n`, the degree the relation `∂ h = f + f'` requires. Along a
  type `D` structure whose structure map has degree `l`, the induced map
  `T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` of box tensor products then has degree `c`
  (`TauCeti.TypeDStructure.typeABoxMapOfHom_mem_boxGradedPart`), and the induced homotopy `T_H`
  has degree `l⁻¹ c` (`TauCeti.TypeDStructure.typeABoxHomotopy_mem_boxGradedPart`). These are
  the graded refinements of the functoriality and homotopy invariance of the box tensor product
  in the type `A` module (`TauCeti.LowDimTopology.Bordered.TypeA.Invariance`): a homotopy
  equivalence of graded type `A` modules by homogeneous morphisms and homotopies of degree `1`
  induces maps of box tensor products of degree `1` and homotopies of degree `l⁻¹`. Since only the
  components of `f` and `h` enter `T_f` and `T_H`, neither statement needs the operations of the
  modules to be graded.

## Main definitions

* `TauCeti.UngradedAInfinityRightModule.IsGraded`: an `A∞` right module graded by a `G`-set,
  with `m_{n+1}` of degree `λ^{n-1}`.
* `TauCeti.UngradedAInfinityRightModuleHom.IsHomogeneous`: a morphism of graded `A∞` modules
  homogeneous of degree `c`, with `f_{n+1}` of degree `c λ^n`.
* `TauCeti.UngradedAInfinityRightModuleHom.Homotopy.IsHomogeneous`: a homotopy with `h_{n+1}` of
  degree `l⁻¹ c λ^n`.

## Main results

* `TauCeti.IsUngradedDGRightModule.isGraded_toUngradedAInfinityRightModule_iff`: the gradings of
  a differential module as an `A∞` module.
* `TauCeti.UngradedAInfinityRightModule.IsGraded.matrixAct_mem_boxGradedPart`: the operations of
  the matrix module along homogeneous matrices.
* `TauCeti.TypeDStructure.typeABoxDifferential_mem_boxGradedPart`: the box tensor differential
  of a graded `A∞` module with a graded type `D` structure is homogeneous of degree `l`.
* `TauCeti.TypeDStructure.typeABoxMap_mem_boxGradedPart` and
  `TauCeti.TypeDStructure.typeABoxCompHomotopy_mem_boxGradedPart`: the induced maps and the
  composition homotopies are homogeneous.
* `TauCeti.UngradedAInfinityRightModuleHom.isHomogeneous_id`,
  `TauCeti.UngradedAInfinityRightModuleHom.IsHomogeneous.add` and
  `TauCeti.UngradedAInfinityRightModuleHom.IsHomogeneous.comp`: identities, sums and composites of
  homogeneous morphisms.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_mem_boxGradedPart` and
  `TauCeti.TypeDStructure.typeABoxHomotopy_mem_boxGradedPart`: homogeneous morphisms and
  homotopies of type `A` modules induce homogeneous maps and homotopies of box tensor products.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §2.5
  (gradings of `A∞` modules by `G`-sets, with `m_{n+1}` of degree `λ^{n-1}`, and of the box
  tensor product by the balanced product of the grading sets).
-/

public section

open MulOpposite

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {G : Type*} [Group G]
  {Ag : G → Submodule R A} {M : Type*} [AddCommGroup M] [Module R M] {S : Type*} [MulAction G S]
  {Mg : S → Submodule R M} {d : A →ₗ[R] A}

/-! ### Graded `A∞` modules -/

namespace UngradedAInfinityRightModule

/-- An `A∞` right module is **graded** by `Mg : S → Submodule R M` over the grading `Ag` of the
algebra, with central degree `l` of the differentials (`λ⁻¹` in the bordered algebras), when its
operation `m_{n+1}` has degree `λ^{n-1} = l^{1-n}`: for `m` of degree `s` and inputs `aᵢ` of
degrees `gᵢ`, `m_{n+1}(m, a₁, …, aₙ)` has degree `s · l^{1-n} g₁ ⋯ gₙ`, where the right action is
`s · g = g⁻¹ • s`. -/
def IsGraded (Mm : UngradedAInfinityRightModule d M) (Ag : G → Submodule R A)
    (Mg : S → Submodule R M) (l : G) : Prop :=
  ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
    m ∈ Mg s → Mm.act n a m ∈ Mg ((List.ofFn g).prod⁻¹ • l ^ ((n : ℤ) - 1) • s)

variable {Mm : UngradedAInfinityRightModule d M} {l : G}

/-- The definition of a graded `A∞` module, unfolded. -/
theorem isGraded_iff : Mm.IsGraded Ag Mg l ↔
    ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
      m ∈ Mg s → Mm.act n a m ∈ Mg ((List.ofFn g).prod⁻¹ • l ^ ((n : ℤ) - 1) • s) :=
  Iff.rfl

namespace IsGraded

/-- The operation `m_{n+1}` of a graded `A∞` module has degree `l^{1-n}`. -/
theorem act_mem (hMm : Mm.IsGraded Ag Mg l) {n : ℕ} {g : Fin n → G} {a : Fin n → A} {s : S}
    {m : M} (ha : ∀ i, a i ∈ Ag (g i)) (hm : m ∈ Mg s) :
    Mm.act n a m ∈ Mg ((List.ofFn g).prod⁻¹ • l ^ ((n : ℤ) - 1) • s) :=
  hMm n g a s m ha hm

/-- The differential `m₁` of a graded `A∞` module has degree `l`. -/
theorem act_zero_mem (hMm : Mm.IsGraded Ag Mg l) (a : Fin 0 → A) {s : S} {m : M}
    (hm : m ∈ Mg s) : Mm.act 0 a m ∈ Mg (l⁻¹ • s) := by
  simpa using hMm.act_mem (g := Fin.elim0) (fun i ↦ i.elim0) hm

/-- The operation `m₂` of a graded `A∞` module is a graded right action. -/
theorem act_one_mem (hMm : Mm.IsGraded Ag Mg l) {a : Fin 1 → A} {g : G} (ha : a 0 ∈ Ag g)
    {s : S} {m : M} (hm : m ∈ Mg s) : Mm.act 1 a m ∈ Mg (g⁻¹ • s) := by
  simpa using hMm.act_mem (n := 1) (g := fun _ ↦ g) (fun i ↦ by rwa [Subsingleton.elim i 0]) hm

end IsGraded

end UngradedAInfinityRightModule

namespace IsUngradedDGRightModule

variable [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] {dM : M →ₗ[R] M} {l : G}

/-- **The gradings of a differential module as an `A∞` module.** A differential right module,
viewed as an `A∞` module, is graded with differentials of degree `l` exactly when its right action
is graded, `Mg s * Ag g ⊆ Mg (g⁻¹ • s)`, and its differential has degree `l`,
`dM (Mg s) ⊆ Mg (l⁻¹ • s)`: these are the hypotheses on differential modules in
`TauCeti.TypeDStructure.boxDifferential_mem_boxGradedPart`. -/
theorem isGraded_toUngradedAInfinityRightModule_iff [CharP R 2]
    (hM : IsUngradedDGRightModule d dM) :
    hM.toUngradedAInfinityRightModule.IsGraded Ag Mg l ↔
      (∀ {s : S} {g : G} {m : M} {a : A}, m ∈ Mg s → a ∈ Ag g → op a • m ∈ Mg (g⁻¹ • s)) ∧
        ∀ {s : S} {m : M}, m ∈ Mg s → dM m ∈ Mg (l⁻¹ • s) := by
  refine ⟨fun h ↦ ⟨fun {s g m a} hm ha ↦ ?_, fun {s m} hm ↦ ?_⟩, fun ⟨hact, hdM⟩ ↦ ?_⟩
  · simpa using h.act_one_mem (a := fun _ ↦ a) ha hm
  · simpa using h.act_zero_mem Fin.elim0 hm
  · intro n g a s m ha hm
    match n with
    | 0 => simpa using hdM hm
    | 1 => simpa using hact hm (ha 0)
    | n + 2 =>
      rw [toUngradedAInfinityRightModule_act_add_two]
      exact zero_mem _

end IsUngradedDGRightModule

/-- **A graded differential algebra is a graded type `A` module over itself.** Let `A` be graded by
`Ag`, with `Ag g * Ag h ⊆ Ag (g * h)`, and let its differential have central degree `l`. Then `A`,
as an `A∞` right module over itself, is graded over the regular `G`-set by `Mg s = Ag s⁻¹`, with
differentials of degree `l`. -/
theorem IsUngradedDGAlgebra.isGraded_toUngradedAInfinityRightModule [CharP R 2]
    (hd : IsUngradedDGAlgebra d)
    (hA : ∀ {g h : G} {a b : A}, a ∈ Ag g → b ∈ Ag h → a * b ∈ Ag (g * h))
    {l : Subgroup.center G} (hdl : ∀ {g : G} {a : A}, a ∈ Ag g → d a ∈ Ag (l * g)) :
    hd.isUngradedDGRightModule.toUngradedAInfinityRightModule.IsGraded Ag (fun s : G ↦ Ag s⁻¹)
      l := by
  refine (IsUngradedDGRightModule.isGraded_toUngradedAInfinityRightModule_iff _).2
    ⟨fun {s g m a} hm ha ↦ ?_, fun {s m} hm ↦ ?_⟩
  · rw [op_smul_eq_mul, smul_eq_mul, mul_inv_rev, inv_inv]
    exact hA hm ha
  · rw [smul_eq_mul, mul_inv_rev, inv_inv, Subgroup.mem_center_iff.mp l.property s⁻¹]
    exact hdl hm

/-! ### Homogeneous morphisms and homotopies of graded `A∞` modules -/

namespace UngradedAInfinityRightModuleHom

variable {M' M'' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
  {Mg' : S → Submodule R M'} {Mg'' : S → Submodule R M''} {Mm : UngradedAInfinityRightModule d M}
  {Mm' : UngradedAInfinityRightModule d M'} {Mm'' : UngradedAInfinityRightModule d M''}

/-- A morphism `f` of `A∞` modules graded over the same `G`-set, with differentials of central
degree `l` (`λ⁻¹` in the bordered algebras), is **homogeneous of degree `c`** when its component
`f_{n+1}` has degree `c λ^n = c l^{-n}`: for `m` of degree `s` and inputs `aᵢ` of degrees `gᵢ`,
`f_{n+1}(m, a₁, …, aₙ)` has degree `s · c l^{-n} g₁ ⋯ gₙ`, where the right action is
`s · g = g⁻¹ • s`. So `f₁` has degree `c`, and a homomorphism of graded modules is homogeneous
of degree `1`. -/
def IsHomogeneous (f : UngradedAInfinityRightModuleHom Mm Mm') (Ag : G → Submodule R A)
    (Mg : S → Submodule R M) (Mg' : S → Submodule R M') (l c : G) : Prop :=
  ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
    m ∈ Mg s → f.map n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • l ^ n • c⁻¹ • s)

/-- The definition of a homogeneous morphism, unfolded. -/
theorem isHomogeneous_iff {f : UngradedAInfinityRightModuleHom Mm Mm'} {l c : G} :
    f.IsHomogeneous Ag Mg Mg' l c ↔
      ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
        m ∈ Mg s → f.map n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • l ^ n • c⁻¹ • s) :=
  Iff.rfl

/-- The component `f_{n+1}` of a morphism homogeneous of degree `c` has degree `c l^{-n}`. -/
theorem IsHomogeneous.map_mem {f : UngradedAInfinityRightModuleHom Mm Mm'} {l c : G}
    (hf : f.IsHomogeneous Ag Mg Mg' l c) {n : ℕ} {g : Fin n → G} {a : Fin n → A} {s : S} {m : M}
    (ha : ∀ i, a i ∈ Ag (g i)) (hm : m ∈ Mg s) :
    f.map n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • l ^ n • c⁻¹ • s) :=
  hf n g a s m ha hm

/-- The sum of two morphisms homogeneous of degree `c` is homogeneous of degree `c`. -/
theorem IsHomogeneous.add {f f' : UngradedAInfinityRightModuleHom Mm Mm'} {l c : G}
    (hf : f.IsHomogeneous Ag Mg Mg' l c) (hf' : f'.IsHomogeneous Ag Mg Mg' l c) :
    (f + f').IsHomogeneous Ag Mg Mg' l c := fun n g a s m ha hm ↦ by
  rw [add_map, add_apply, LinearMap.add_apply]
  exact add_mem (hf.map_mem ha hm) (hf'.map_mem ha hm)

/-- **Strict morphisms of graded modules.** Over a ring of characteristic two, a linear map
preserving the gradings and commuting with the operations is a morphism homogeneous of degree
`1`. -/
theorem isHomogeneous_ofLinearMap [CharP R 2] (L : M →ₗ[R] M')
    (hL : ∀ n a m, L (Mm.act n a m) = Mm'.act n a (L m))
    (hLg : ∀ {s : S} {m : M}, m ∈ Mg s → L m ∈ Mg' s) (l : G) :
    (ofLinearMap Mm Mm' L hL).IsHomogeneous Ag Mg Mg' l 1 := by
  intro n g a s m ha hm
  match n with
  | 0 => simpa using hLg hm
  | n + 1 =>
    rw [ofLinearMap_map_add_one]
    exact zero_mem _

/-- The identity morphism of a graded module is homogeneous of degree `1`. -/
theorem isHomogeneous_id [CharP R 2] (l : G) : (id Mm).IsHomogeneous Ag Mg Mg l 1 := by
  intro n g a s m ha hm
  match n with
  | 0 => simpa using hm
  | n + 1 =>
    rw [id_map_add_one]
    exact zero_mem _

/-- The degree bookkeeping of a composite: the central factors `l ^ j c'⁻¹` of the second
morphism move past the degree `P` of the inputs of the first. -/
private theorem inv_mul_pow_mul_inv_eq (P Q c : G) (l c' : Subgroup.center G) (i j : ℕ) :
    (P * Q)⁻¹ * ((l : G) ^ (i + j) * (c * c')⁻¹) =
      Q⁻¹ * ((l : G) ^ j * ((c' : G)⁻¹ * (P⁻¹ * ((l : G) ^ i * c⁻¹)))) := by
  have hz : ((l ^ j * c'⁻¹ : Subgroup.center G) : G) * P⁻¹ =
      P⁻¹ * ((l ^ j * c'⁻¹ : Subgroup.center G) : G) :=
    (Subgroup.mem_center_iff.mp (l ^ j * c'⁻¹).property P⁻¹).symm
  have hzw : (l ^ (i + j) * c'⁻¹ : Subgroup.center G) = l ^ j * c'⁻¹ * l ^ i := by
    rw [pow_add]
    ac_rfl
  have hzw' := congrArg (fun z : Subgroup.center G ↦ (z : G)) hzw
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at hz hzw'
  calc (P * Q)⁻¹ * ((l : G) ^ (i + j) * (c * c')⁻¹)
      = Q⁻¹ * P⁻¹ * ((l : G) ^ (i + j) * (c' : G)⁻¹ * c⁻¹) := by
        simp only [mul_inv_rev, mul_assoc]
    _ = Q⁻¹ * (P⁻¹ * ((l : G) ^ j * (c' : G)⁻¹)) * ((l : G) ^ i * c⁻¹) := by
        rw [hzw']
        simp only [mul_assoc]
    _ = Q⁻¹ * ((l : G) ^ j * ((c' : G)⁻¹ * (P⁻¹ * ((l : G) ^ i * c⁻¹)))) := by
        rw [← hz]
        simp only [mul_assoc]

/-- **Composites of homogeneous morphisms.** Over a ring of characteristic two, for central `l`
and `c'`, the composite of morphisms homogeneous of degrees `c` and `c'` is homogeneous of degree
`c c'`: the component `(f' ∘ f)_{n+1}` is a sum of terms
`f'_{j+1}(f_{i+1}(m, a₁, …, aᵢ), aᵢ₊₁, …, aₙ)` of degree `s · (c l^{-i} g₁ ⋯ gᵢ)
(c' l^{-j} gᵢ₊₁ ⋯ gₙ) = s · c c' l^{-n} g₁ ⋯ gₙ`. -/
theorem IsHomogeneous.comp [CharP R 2] {f : UngradedAInfinityRightModuleHom Mm Mm'}
    {f' : UngradedAInfinityRightModuleHom Mm' Mm''} {c : G} {l c' : Subgroup.center G}
    (hf : f.IsHomogeneous Ag Mg Mg' l c) (hf' : f'.IsHomogeneous Ag Mg' Mg'' l c') :
    (f'.comp f).IsHomogeneous Ag Mg Mg'' l (c * c') := by
  intro n g a s m ha hm
  rw [comp_map_apply]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  have h := hf'.map_mem (g := fun i : Fin (n - k) ↦ g ⟨k + i, by have := i.isLt; omega⟩)
    (fun i ↦ ha _) (hf.map_mem (g := fun i : Fin k ↦ g ⟨i, by have := i.isLt; omega⟩)
      (fun i ↦ ha _) hm)
  convert h using 2
  have hn : (k : ℕ) + (n - k) = n := by have := k.isLt; omega
  have hpow : (l : G) ^ n = (l : G) ^ ((k : ℕ) + (n - k)) := by rw [hn]
  simp only [← mul_smul]
  rw [← List.prod_ofFn_mul_prod_ofFn (k := k) (by omega) g, hpow, inv_mul_pow_mul_inv_eq]

/-- A homotopy `H` between two morphisms homogeneous of degree `c` is **homogeneous** when its
component `h_{n+1}` has degree `l⁻¹ c λ^n = l⁻¹ c l^{-n}`, one `l` below the components of the
morphisms: for `m` of degree `s` and inputs `aᵢ` of degrees `gᵢ`, `h_{n+1}(m, a₁, …, aₙ)` has
degree `s · l⁻¹ c l^{-n} g₁ ⋯ gₙ`. This is the degree that the homotopy relation `∂ h = f + f'`
requires. -/
def Homotopy.IsHomogeneous {f f' : UngradedAInfinityRightModuleHom Mm Mm'} (H : Homotopy f f')
    (Ag : G → Submodule R A) (Mg : S → Submodule R M) (Mg' : S → Submodule R M') (l c : G) :
    Prop :=
  ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
    m ∈ Mg s → H.map n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • l ^ (n + 1) • c⁻¹ • s)

/-- The definition of a homogeneous homotopy, unfolded. -/
theorem Homotopy.isHomogeneous_iff {f f' : UngradedAInfinityRightModuleHom Mm Mm'}
    {H : Homotopy f f'} {l c : G} :
    H.IsHomogeneous Ag Mg Mg' l c ↔
      ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
        m ∈ Mg s → H.map n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • l ^ (n + 1) • c⁻¹ • s) :=
  Iff.rfl

/-- The component `h_{n+1}` of a homogeneous homotopy between morphisms of degree `c` has degree
`l⁻¹ c l^{-n}`. -/
theorem Homotopy.IsHomogeneous.map_mem {f f' : UngradedAInfinityRightModuleHom Mm Mm'}
    {H : Homotopy f f'} {l c : G} (hH : H.IsHomogeneous Ag Mg Mg' l c) {n : ℕ} {g : Fin n → G}
    {a : Fin n → A} {s : S} {m : M} (ha : ∀ i, a i ∈ Ag (g i)) (hm : m ∈ Mg s) :
    H.map n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • l ^ (n + 1) • c⁻¹ • s) :=
  hH n g a s m ha hm

end UngradedAInfinityRightModuleHom

/-! ### Gradings of box tensor products -/

namespace UngradedAInfinityRightModule

variable {T : Type*} [MulAction G T] {X : Type*}

variable [Fintype X] [DecidableEq X] {Mm : UngradedAInfinityRightModule d M}

/-- **The operations of the matrix module along homogeneous matrices.** Let `M` be a graded `A∞`
module with differentials of central degree `l`, and let `F₁, …, Fₙ` be matrices homogeneous of
degree `l`. Then `m_{n+1}(φ, F₁, …, Fₙ)` maps row vectors of degree `u ∈ S ×_G T` to row vectors
of degree `l • u`: the operation has degree `l^{1-n}` and the matrices contribute `l^n`. -/
theorem IsGraded.matrixAct_mem_boxGradedPart {l : Subgroup.center G}
    (hMm : Mm.IsGraded Ag Mg l) {gr : X → T} {n : ℕ} {F : Fin n → Matrix X X A}
    (hF : ∀ i, F i ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) : Mm.matrixAct X n F φ ∈ boxGradedPart Mg gr (l • u) := by
  rw [mem_boxGradedPart_iff] at hφ ⊢
  intro z
  rw [matrixAct_apply]
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  split_ifs with hz
  swap
  · exact zero_mem _
  refine Submodule.iSup_induction _
    (motive := fun m ↦ Mm.act n (fun i ↦ F i (x i.castSucc) (x i.succ)) m ∈ _) (hφ (x 0)) ?_
    (by rw [map_zero]; exact zero_mem _) fun m m' hm hm' ↦ by rw [map_add]; exact add_mem hm hm'
  rintro ⟨s, hs⟩ m hm
  -- The entries along the path are sums of homogeneous elements; by multilinearity it suffices to
  -- treat homogeneous entries.
  refine ((LinearMap.applyₗ m).compMultilinearMap (Mm.act n)).map_mem_of_mem_homogeneousMatrices hF
    x fun g a hg ha ↦ Submodule.mem_iSup_of_mem ⟨_, ?_⟩ (hMm.act_mem ha hm)
  rw [← hz, BalancedProduct.mk_inv_prod_ofFn_zpow_smul l g (fun j ↦ gr (x j)) hg, hs]

/-- **The twisted differential of the matrix module along a homogeneous matrix.** For a graded
`A∞` module with differentials of central degree `l` and a matrix `C` homogeneous of degree `l`,
the twisted differential `∑ₙ m_{n+1}(·, C, …, C)` of the matrix module maps row vectors of degree
`u` to row vectors of degree `l • u`. No boundedness is needed: an infinite sum is `0` by the
convention of `TauCeti.UngradedAInfinityRightModule.twistedDifferential`. -/
theorem IsGraded.twistedDifferential_matrix_mem_boxGradedPart {l : Subgroup.center G}
    (hMm : Mm.IsGraded Ag Mg l) {gr : X → T} {C : Matrix X X A}
    (hC : C ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) :
    (Mm.matrix X).twistedDifferential C φ ∈ boxGradedPart Mg gr (l • u) := by
  rw [twistedDifferential_def]
  refine finsum_induction (fun P : (X → M) →ₗ[R] X → M ↦ P φ ∈ boxGradedPart Mg gr (l • u))
    (zero_mem _) (fun P P' hP hP' ↦ add_mem hP hP') fun n ↦ ?_
  rw [matrix_act]
  exact hMm.matrixAct_mem_boxGradedPart (fun _ ↦ hC) hφ

end UngradedAInfinityRightModule

namespace TypeDStructure

variable {K : Type*} {ι : K → A} {T : Type*} [MulAction G T] {X X' X'' : Type*} [Fintype X]
  [DecidableEq X] [Fintype X'] [DecidableEq X'] {Mm : UngradedAInfinityRightModule d M}

/-- **The box tensor differential of a graded `A∞` module is homogeneous.** Let `M` be graded
with differentials of central degree `l`, and let the structure map of `N` have degree `l`. Then
the box tensor differential `∂ (m ⊗ x) = ∑_k (m_{k+1} ⊗ 1) (m ⊗ δ^k (x))` maps row vectors of
degree `u ∈ S ×_G T` to row vectors of degree `l • u`. -/
theorem typeABoxDifferential_mem_boxGradedPart {l : Subgroup.center G}
    (hMm : Mm.IsGraded Ag Mg l) {N : TypeDStructure d ι X} {gr : X → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l) {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) :
    N.typeABoxDifferential Mm φ ∈ boxGradedPart Mg gr (l • u) := by
  rw [typeABoxDifferential_def]
  exact hMm.twistedDifferential_matrix_mem_boxGradedPart hN hφ

/-- **Induced maps of graded box tensor products.** Let `M` be a graded `A∞` module with
differentials of central degree `l`, let the structure maps of `N` and `N'` have degree `l`, and
let the morphism `F` from `N` to `N'` be homogeneous of central degree `c`. Then the induced map
`T_F` from `M ⊠ N` to `M ⊠ N'` maps row vectors of degree `u` to row vectors of degree `c • u`;
homomorphisms of degree `1` induce graded maps. -/
theorem typeABoxMap_mem_boxGradedPart {l : Subgroup.center G} (hMm : Mm.IsGraded Ag Mg l)
    {N : TypeDStructure d ι X} {N' : TypeDStructure d ι X'} {gr : X → T} {gr' : X' → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    (hN' : N'.coeff ∈ homogeneousMatrices Ag gr' gr' l) {c : Subgroup.center G}
    {F : Matrix X X' A} (hF : F ∈ homogeneousMatrices Ag gr gr' c) {u : BalancedProduct G S T}
    {φ : X → M} (hφ : φ ∈ boxGradedPart Mg gr u) :
    typeABoxMap N N' Mm F φ ∈ boxGradedPart Mg gr' (c • u) := by
  -- Translating the grading of `X'` by `k = l c⁻¹` makes `fromBlocks δ F 0 δ'` homogeneous of
  -- degree `l`, so the induced map is a component of a homogeneous box tensor differential.
  set k : Subgroup.center G := l * c⁻¹
  have hF' : F ∈ homogeneousMatrices Ag gr (fun y ↦ (k : G) • gr' y) l := by
    simpa [k] using (mem_homogeneousMatrices_smul_right_iff k.property).2 hF
  have hC : Matrix.fromBlocks N.coeff F 0 N'.coeff ∈
      homogeneousMatrices Ag (Sum.elim gr fun y ↦ (k : G) • gr' y)
        (Sum.elim gr fun y ↦ (k : G) • gr' y) l :=
    fromBlocks_mem_homogeneousMatrices_iff.2
      ⟨hN, hF', zero_mem _, (mem_homogeneousMatrices_smul_smul_iff k.property).2 hN'⟩
  rw [mem_boxGradedPart_iff]
  intro z
  rw [typeABoxMap_apply]
  have hk : k⁻¹ * l = c := by simp [k]
  rw [← hk, mul_smul]
  exact mem_iSup_mk_smul_iff.mp
    (hMm.twistedDifferential_matrix_mem_boxGradedPart hC
      (sumElim_zero_mem_boxGradedPart hφ) |> mem_boxGradedPart_iff.mp <| Sum.inr z)

/-- **The composition homotopies of graded box tensor products.** Let `M` be a graded `A∞` module
with differentials of central degree `l`, let the structure maps of `N`, `N'` and `N''` have
degree `l`, and let the morphisms `F` from `N` to `N'` and `G'` from `N'` to `N''` be homogeneous
of central degrees `c` and `c'`. Then `K = TauCeti.TypeDStructure.typeABoxCompHomotopy` maps row
vectors of degree `u` to row vectors of degree `(l⁻¹ * c * c') • u`, one `l` below the degree of
the composite. Over a ring of characteristic two, when `F` and `G'` are homomorphisms and `M`, or
`N`, `N'` and `N''`, are bounded, `K` satisfies `T_{G'} ∘ T_F + T_{F G'} = ∂'' ∘ K + K ∘ ∂`
(`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero` and
`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt`), so this is the degree
that equation requires. -/
theorem typeABoxCompHomotopy_mem_boxGradedPart [Fintype X''] [DecidableEq X'']
    {l : Subgroup.center G} (hMm : Mm.IsGraded Ag Mg l) {N : TypeDStructure d ι X}
    {N' : TypeDStructure d ι X'} {N'' : TypeDStructure d ι X''} {gr : X → T} {gr' : X' → T}
    {gr'' : X'' → T}
    (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    (hN' : N'.coeff ∈ homogeneousMatrices Ag gr' gr' l)
    (hN'' : N''.coeff ∈ homogeneousMatrices Ag gr'' gr'' l) {c c' : Subgroup.center G}
    {F : Matrix X X' A} (hF : F ∈ homogeneousMatrices Ag gr gr' c) {G' : Matrix X' X'' A}
    (hG' : G' ∈ homogeneousMatrices Ag gr' gr'' c') {u : BalancedProduct G S T} {φ : X → M}
    (hφ : φ ∈ boxGradedPart Mg gr u) :
    typeABoxCompHomotopy N N' N'' Mm F G' φ ∈ boxGradedPart Mg gr'' ((l⁻¹ * c * c') • u) := by
  -- Translating the gradings of `X'` by `k = l c⁻¹` and of `X''` by `k' = l c'⁻¹ k` makes the
  -- block matrix with diagonal `δ, δ', δ''` and off-diagonal blocks `F`, `G'` homogeneous of
  -- degree `l`.
  set k : Subgroup.center G := l * c⁻¹
  set k' : Subgroup.center G := l * c'⁻¹ * k
  have hF' : F ∈ homogeneousMatrices Ag gr (fun y ↦ (k : G) • gr' y) l := by
    simpa [k] using (mem_homogeneousMatrices_smul_right_iff k.property).2 hF
  have hG'' : G' ∈ homogeneousMatrices Ag (fun y ↦ (k : G) • gr' y)
      (fun z ↦ (k' : G) • gr'' z) l := by
    have h := (mem_homogeneousMatrices_smul_right_iff (l * c'⁻¹ : Subgroup.center G).property
      (gr' := fun z ↦ (k : G) • gr'' z)).2 ((mem_homogeneousMatrices_smul_smul_iff k.property).2
          hG')
    simpa [k', mul_smul] using h
  have hC : Matrix.fromBlocks N.coeff (Matrix.fromCols F 0) 0
      (Matrix.fromBlocks N'.coeff G' 0 N''.coeff) ∈
      homogeneousMatrices Ag
        (Sum.elim gr (Sum.elim (fun y ↦ (k : G) • gr' y) fun z ↦ (k' : G) • gr'' z))
        (Sum.elim gr (Sum.elim (fun y ↦ (k : G) • gr' y) fun z ↦ (k' : G) • gr'' z)) l :=
    fromBlocks_mem_homogeneousMatrices_iff.2 ⟨hN,
      fromCols_mem_homogeneousMatrices_iff.2 ⟨hF', zero_mem _⟩, zero_mem _,
      fromBlocks_mem_homogeneousMatrices_iff.2 ⟨(mem_homogeneousMatrices_smul_smul_iff k.property).2
          hN',
        hG'', zero_mem _, (mem_homogeneousMatrices_smul_smul_iff k'.property).2 hN''⟩⟩
  rw [mem_boxGradedPart_iff]
  intro z
  rw [typeABoxCompHomotopy_apply]
  have hk : k'⁻¹ * l = l⁻¹ * c * c' := by
    have hcomm (a b : Subgroup.center G) : a * b = b * a :=
      Subtype.ext (Subgroup.mem_center_iff.mp b.property a)
    rw [← hcomm c l⁻¹]
    simp only [k', k]
    group
  rw [← hk, mul_smul]
  exact mem_iSup_mk_smul_iff.mp
    (hMm.twistedDifferential_matrix_mem_boxGradedPart hC
      (sumElim_zero_mem_boxGradedPart hφ) |> mem_boxGradedPart_iff.mp <| Sum.inr (Sum.inr z))

/-! ### Maps and homotopies induced by homogeneous morphisms of type `A` modules -/

section ModuleHom

variable {M' : Type*} [AddCommGroup M'] [Module R M'] {Mg' : S → Submodule R M'}
  {Mm' : UngradedAInfinityRightModule d M'}

/-- The class of a central translate `c • s` of a module degree is `c⁻¹` times the class of `s`. -/
private theorem mk_center_smul_left (c : Subgroup.center G) (s : S) (t : T) :
    BalancedProduct.mk G ((c : G) • s) t = c⁻¹ • BalancedProduct.mk G s t := by
  rw [BalancedProduct.mk_smul_left, BalancedProduct.center_smul_mk, Subgroup.coe_inv]

/-- Along the paths of a matrix homogeneous of degree `l`, a family of maps whose `n`-th member
shifts degrees by `l^n k⁻¹` on the left carries a row vector of degree `u` to entries of degree
`k • u`. -/
private theorem sum_ite_map_mem
    {Φ : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n ↦ A) (M →ₗ[R] M')}
    {l k : Subgroup.center G}
    (hΦ : ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
      m ∈ Mg s → Φ n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • (l : G) ^ n • (k : G)⁻¹ • s))
    {gr : X → T} {C : Matrix X X A} (hC : C ∈ homogeneousMatrices Ag gr gr l)
    {u : BalancedProduct G S T} {φ : X → M} (hφ : φ ∈ boxGradedPart Mg gr u) (n : ℕ) (z : X) :
    (∑ x : Fin (n + 1) → X, if x (Fin.last n) = z then
        Φ n (fun i ↦ C (x i.castSucc) (x i.succ)) (φ (x 0)) else 0) ∈
      ⨆ s : {s : S // BalancedProduct.mk G s (gr z) = k • u}, Mg' s := by
  rw [mem_boxGradedPart_iff] at hφ
  refine Submodule.sum_mem _ fun x _ ↦ ?_
  split_ifs with hz
  swap
  · exact zero_mem _
  refine Submodule.iSup_induction _
    (motive := fun m ↦ Φ n (fun i ↦ C (x i.castSucc) (x i.succ)) m ∈ _) (hφ (x 0)) ?_
    (by rw [map_zero]; exact zero_mem _) fun m m' hm hm' ↦ by rw [map_add]; exact add_mem hm hm'
  rintro ⟨s, hs⟩ m hm
  refine ((LinearMap.applyₗ m).compMultilinearMap (Φ n)).map_mem_of_mem_homogeneousMatrices
    (fun _ ↦ hC) x fun g a hg ha ↦ Submodule.mem_iSup_of_mem ⟨_, ?_⟩ (hΦ n g a s m ha hm)
  rw [← hz, BalancedProduct.mk_inv_prod_ofFn_smul l g (fun j ↦ gr (x j)) hg, ← Subgroup.coe_pow,
    ← Subgroup.coe_inv, mk_center_smul_left, mk_center_smul_left, hs, smul_smul, mul_inv_cancel,
    one_smul, inv_inv]

/-- The map induced by a morphism `f` whose component `f_{n+1}` shifts degrees by `l^n k⁻¹` on
the left maps row vectors of degree `u` to row vectors of degree `k • u`. -/
private theorem typeABoxMapOfHom_mem_boxGradedPart_of_forall
    {f : UngradedAInfinityRightModuleHom Mm Mm'} {l k : Subgroup.center G}
    (hf : ∀ (n : ℕ) (g : Fin n → G) (a : Fin n → A) (s : S) (m : M), (∀ i, a i ∈ Ag (g i)) →
      m ∈ Mg s → f.map n a m ∈ Mg' ((List.ofFn g).prod⁻¹ • (l : G) ^ n • (k : G)⁻¹ • s))
    {N : TypeDStructure d ι X} {gr : X → T} (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    {u : BalancedProduct G S T} {φ : X → M} (hφ : φ ∈ boxGradedPart Mg gr u) :
    N.typeABoxMapOfHom f φ ∈ boxGradedPart Mg' gr (k • u) := by
  rw [mem_boxGradedPart_iff]
  intro z
  rw [typeABoxMapOfHom_apply, typeABoxDifferential_def,
    UngradedAInfinityRightModule.twistedDifferential_def]
  refine finsum_induction (fun P : (X → M × M') →ₗ[R] X → M × M' ↦
      (P (fun x ↦ (φ x, 0)) z).2 ∈ ⨆ s : {s : S // BalancedProduct.mk G s (gr z) = k • u}, Mg' s)
    ?_ (fun P P' hP hP' ↦ ?_) fun n ↦ ?_
  · simp
  · simpa using add_mem hP hP'
  -- Only the component of `f` survives on row vectors with values in `M`.
  have h0 : (Mm'.matrixAct X n fun _ ↦ N.coeff) (fun _ ↦ (0 : M')) = 0 := map_zero _
  have h := sum_ite_map_mem (Φ := f.map) hf hN hφ n z
  simpa [UngradedAInfinityRightModuleHom.matrixAct_cone_apply, h0] using h

/-- **Maps induced by homogeneous morphisms of graded type `A` modules.** Let the structure map of
`N` have central degree `l`, and let the morphism `f` of graded `A∞` modules be homogeneous of
central degree `c`. Then the induced map `T_f (m ⊗ x) = ∑_k (f_{k+1} ⊗ 1) (m ⊗ δ^k (x))` from
`M ⊠ N` to `M' ⊠ N` maps row vectors of degree `u` to row vectors of degree `c • u`; homomorphisms
of degree `1` induce graded maps. Only the components of `f` enter `T_f`, so no grading of the
operations of `M` and `M'` is needed, and no boundedness, since an infinite sum is `0` by the
convention of `TauCeti.UngradedAInfinityRightModule.twistedDifferential`. -/
theorem typeABoxMapOfHom_mem_boxGradedPart {l c : Subgroup.center G}
    {f : UngradedAInfinityRightModuleHom Mm Mm'} (hf : f.IsHomogeneous Ag Mg Mg' l c)
    {N : TypeDStructure d ι X} {gr : X → T} (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    {u : BalancedProduct G S T} {φ : X → M} (hφ : φ ∈ boxGradedPart Mg gr u) :
    N.typeABoxMapOfHom f φ ∈ boxGradedPart Mg' gr (c • u) :=
  typeABoxMapOfHom_mem_boxGradedPart_of_forall hf hN hφ

/-- **Homotopies induced by homogeneous homotopies of graded type `A` modules.** Over a ring of
characteristic two, let the structure map of `N` have central degree `l`, and let `H` be a
homogeneous homotopy between two morphisms of graded `A∞` modules homogeneous of central degree
`c`. Then the induced homotopy `T_H (m ⊗ x) = ∑_k (h_{k+1} ⊗ 1) (m ⊗ δ^k (x))` maps row vectors of
degree `u` to row vectors of degree `(l⁻¹ * c) • u`, one `l` below the degree of the maps it
relates. This is the degree that the homotopy equation
`T_f + T_{f'} = ∂' ∘ T_H + T_H ∘ ∂` requires
(`TauCeti.TypeDStructure.typeABoxMapOfHom_add_typeABoxMapOfHom_of_isBounded`). -/
theorem typeABoxHomotopy_mem_boxGradedPart [CharP R 2] {l c : Subgroup.center G}
    {f f' : UngradedAInfinityRightModuleHom Mm Mm'}
    {H : UngradedAInfinityRightModuleHom.Homotopy f f'} (hH : H.IsHomogeneous Ag Mg Mg' l c)
    {N : TypeDStructure d ι X} {gr : X → T} (hN : N.coeff ∈ homogeneousMatrices Ag gr gr l)
    {u : BalancedProduct G S T} {φ : X → M} (hφ : φ ∈ boxGradedPart Mg gr u) :
    N.typeABoxHomotopy H φ ∈ boxGradedPart Mg' gr ((l⁻¹ * c) • u) := by
  -- `T_H` is the second component of the map induced by `(id, h)`, into `M × M'` graded through
  -- its second factor.
  have hT := typeABoxMapOfHom_mem_boxGradedPart_of_forall
    (Mg' := fun s ↦ (Mg' s).comap (LinearMap.snd R M M')) (f := H.toConeHom) (l := l)
    (k := l⁻¹ * c) (fun n g a s m ha hm ↦ ?_) hN hφ
  · rw [mem_boxGradedPart_iff] at hT ⊢
    intro z
    have h := Submodule.mem_map_of_mem (f := LinearMap.snd R M M') (hT z)
    rw [Submodule.map_iSup] at h
    rw [typeABoxHomotopy_apply]
    exact iSup_mono (fun s ↦ Submodule.map_comap_le _ _) h
  · rw [Submodule.mem_comap, UngradedAInfinityRightModuleHom.Homotopy.toConeHom_map_apply,
      LinearMap.snd_apply]
    convert hH.map_mem ha hm using 2
    have hcl : (c : G)⁻¹ * l = l * (c : G)⁻¹ := Subgroup.mem_center_iff.mp l.property _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv, hcl, pow_succ]
    simp only [mul_smul]

end ModuleHom

end TypeDStructure

end TauCeti
