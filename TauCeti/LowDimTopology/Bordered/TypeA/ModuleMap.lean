/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeA

/-!
# Functoriality of the box tensor product in the type `A` module

The box tensor product `M ⊠ N` of an `A∞` right module `M` with a type `D` structure `N`, on row
vectors `X → M` (`TauCeti.LowDimTopology.Bordered.TypeA`), is functorial in the module `M`.

A family of maps `f_{n+1} : M ⊗ A^{⊗ n} → M'`, such as a morphism of `A∞` modules, induces the
map `f ⊠ 𝟙` from `M ⊠ N` to `M' ⊠ N` (`TauCeti.TypeDStructure.typeABoxModuleMap`): the
`z`-component of `(f ⊠ 𝟙) φ` is the sum, over the paths `x₀ → ⋯ → xₙ = z` in `X`, of
`f_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. It is the twist by `δ` of the matrix family of `f`, and the
box tensor differential is the case of the operations of `M`.
Twisting along the Maurer–Cartan element `δ` gives, when `M`, `M'` and `f` are bounded or when `N`
is bounded,

`∂' ∘ (f ⊠ 𝟙) + (f ⊠ 𝟙) ∘ ∂ = (∂f) ⊠ 𝟙`,

where `∂f` is the differential of morphisms
(`TauCeti.UngradedAInfinityRightModule.morphismDifferential`). Unlike in the type `D` variable,
composites and identities are preserved on the nose: `(g ∘ f) ⊠ 𝟙 = (g ⊠ 𝟙) ∘ (f ⊠ 𝟙)` and
`𝟙 ⊠ 𝟙 = 𝟙`, on all row vectors and with no unitality hypothesis. So homomorphisms induce chain
maps, homotopic homomorphisms induce homotopic chain maps, and a homotopy equivalence of `A∞`
modules induces a homotopy equivalence of box tensor products.

The map `T_f` of a morphism `f` of `A∞` modules, defined through its mapping cone
(`TauCeti.TypeDStructure.typeABoxMapOfHom`), is the map `f ⊠ 𝟙` of the components of `f` whenever
the box tensor differential of the cone is a finite sum; these components are a homomorphism
(`TauCeti.UngradedAInfinityRightModuleHom.morphismDifferential_map`).

## Main definitions

* `TauCeti.TypeDStructure.typeABoxModuleMap`: the map of box tensor products induced by a family
  of maps `f_{n+1} : M ⊗ A^{⊗ n} → M'`, such as a morphism of `A∞` modules.

## Main results

* `TauCeti.TypeDStructure.typeABoxDifferential_eq_typeABoxModuleMap`: the box tensor differential
  is the map induced by the operations of the module.
* `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxModuleMap_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxModuleMap_of_isBounded`:
  `∂' ∘ (f ⊠ 𝟙) + (f ⊠ 𝟙) ∘ ∂ = (∂f) ⊠ 𝟙` when the modules and `f`, respectively the type `D`
  structure, are bounded.
* `TauCeti.TypeDStructure.typeABoxModuleMap_ungradedFamilyId`,
  `TauCeti.TypeDStructure.typeABoxModuleMap_ungradedFamilyComp_of_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxModuleMap_ungradedFamilyComp_of_isBounded`: identities and
  composites of `A∞` module maps induce identities and composites.
* `TauCeti.TypeDStructure.typeABoxModuleMap_typeABoxModuleMap_add_of_act_eq_zero` and
  `TauCeti.TypeDStructure.typeABoxModuleMap_typeABoxModuleMap_add_of_isBounded`: homotopy
  equivalences of `A∞` modules induce homotopy equivalences of box tensor products.
* `TauCeti.TypeDStructure.typeABoxMapOfHom_eq_typeABoxModuleMap`: the map induced by a morphism is
  the map induced by its family of components.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (morphisms and homotopies of `A∞` modules, and the box tensor product, equation (2.29),
  with its functoriality in morphisms of `A∞` modules).
-/

public section

open Finset

namespace TauCeti

namespace TypeDStructure

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {d : A →ₗ[R] A} {S : Type*} {ι : S → A} {X : Type*} [Fintype X] [DecidableEq X]
  {M' M'' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']

/-- The **map induced on box tensor products** by a family `f_{n+1} : M ⊗ A^{⊗ n} → M'`, such as a
morphism of `A∞` modules: on row vectors, `φ ↦ ∑ₙ f_{n+1}(φ, δ, …, δ)`, evaluated along the
paths of generators of `N`. It is the twist (`TauCeti.ungradedTwistedMap`) of the matrix family of
`f` by the coefficient matrix `δ` of `N`, the map `f ⊠ 𝟙_N` from `M ⊠ N` to `M' ⊠ N`; for the
operations of a module it is the box tensor differential
(`TauCeti.TypeDStructure.typeABoxDifferential_eq_typeABoxModuleMap`). The sum is finite when `f`,
or `N`, is bounded; otherwise this is `0` by the convention of `TauCeti.ungradedTwistedMap`. -/
noncomputable def typeABoxModuleMap (N : TypeDStructure d ι X)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    (X → M) →ₗ[R] X → M' :=
  ungradedTwistedMap (ungradedMatrixFamily X f) N.coeff

theorem typeABoxModuleMap_def (N : TypeDStructure d ι X)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    N.typeABoxModuleMap f = ungradedTwistedMap (ungradedMatrixFamily X f) N.coeff :=
  (rfl)

/-- The box tensor differential is the map induced by the operations of the module. -/
theorem typeABoxDifferential_eq_typeABoxModuleMap (N : TypeDStructure d ι X)
    (Mm : UngradedAInfinityRightModule d M) :
    N.typeABoxDifferential Mm = N.typeABoxModuleMap Mm.act := by
  rw [typeABoxDifferential_def, typeABoxModuleMap_def,
    UngradedAInfinityRightModule.twistedDifferential_eq_ungradedTwistedMap,
    UngradedAInfinityRightModule.matrix_act,
    UngradedAInfinityRightModule.matrixAct_eq_ungradedMatrixFamily]

/-- **The zero family induces the zero map.** -/
@[simp]
theorem typeABoxModuleMap_zero (N : TypeDStructure d ι X) :
    N.typeABoxModuleMap
      (0 : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) = 0 := by
  simp [typeABoxModuleMap_def]

/-- **The identity induces the identity.** -/
@[simp]
theorem typeABoxModuleMap_ungradedFamilyId (N : TypeDStructure d ι X) :
    N.typeABoxModuleMap (ungradedFamilyId (R := R) (A := A) (M := M)) = LinearMap.id := by
  simp [typeABoxModuleMap_def]

/-- **The induced map as a sum over paths.** When the operations `f_{n+1}(·, δ, …, δ)` of the
matrix family vanish for `n ≥ K`, the `z`-component of `(f ⊠ 𝟙) φ` is the sum, over the paths
`x₀ → ⋯ → xₙ = z` of length `n < K`, of `f_{n+1}(φ x₀, δ x₀ x₁, …, δ xₙ₋₁ xₙ)`. -/
theorem typeABoxModuleMap_apply_eq_sum (N : TypeDStructure d ι X)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) {K : ℕ}
    (hK : ∀ n, K ≤ n → (ungradedMatrixFamily X f n fun _ => N.coeff) = 0) (φ : X → M) (z : X) :
    N.typeABoxModuleMap f φ z = ∑ n ∈ range K, ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then f n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 := by
  rw [typeABoxModuleMap_def, ungradedTwistedMap_eq_sum hK]
  simp only [LinearMap.sum_apply, Finset.sum_apply, ungradedMatrixFamily_apply]

/-- **The map induced by a bounded family as a sum over paths.** If `f_{n+1}` vanishes for
`n ≥ K`, `(f ⊠ 𝟙) φ` is the sum of `TauCeti.TypeDStructure.typeABoxModuleMap_apply_eq_sum` over
the paths of length `n < K`. -/
theorem typeABoxModuleMap_apply_eq_sum_of_eq_zero (N : TypeDStructure d ι X)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) {K : ℕ}
    (hK : ∀ n, K ≤ n → f n = 0) (φ : X → M) (z : X) :
    N.typeABoxModuleMap f φ z = ∑ n ∈ range K, ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then f n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 :=
  N.typeABoxModuleMap_apply_eq_sum f (fun n hn => by
    rw [ungradedMatrixFamily_eq_zero_of_eq_zero (hK n hn), zero_apply]) φ z

/-- **The induced map with a bounded type `D` structure as a sum over paths.** If a height `h` on
the generators strictly increases along every nonzero coefficient of `N`, `(f ⊠ 𝟙) φ` is the sum
of `TauCeti.TypeDStructure.typeABoxModuleMap_apply_eq_sum` over the paths of length `n` at most
the largest height, whatever the family `f`. -/
theorem typeABoxModuleMap_apply_eq_sum_of_lt (N : TypeDStructure d ι X)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (φ : X → M) (z : X) :
    N.typeABoxModuleMap f φ z = ∑ n ∈ range (univ.sup h + 1), ∑ x : Fin (n + 1) → X,
      if x (Fin.last n) = z then f n (fun l => N.coeff (x l.castSucc) (x l.succ)) (φ (x 0))
      else 0 :=
  N.typeABoxModuleMap_apply_eq_sum f
    (fun _ hn => ungradedMatrixFamily_eq_zero_of_lt f h hn fun _ => hh) φ z

section Bounded

variable {Mm : UngradedAInfinityRightModule d M} {Mm' : UngradedAInfinityRightModule d M'}
  {Mm'' : UngradedAInfinityRightModule d M''}

/-- **The induced maps of bounded modules.** Over a ring of characteristic two, if the operations
`m_{k+1}` of `M` and `M'` and the maps `f_{k+1}` vanish for `k ≥ K`, then
`∂' ∘ (f ⊠ 𝟙) + (f ⊠ 𝟙) ∘ ∂ = (∂f) ⊠ 𝟙`, where `∂` and `∂'` are the box tensor differentials and
`∂f` is the differential of morphisms
(`TauCeti.UngradedAInfinityRightModule.morphismDifferential`). -/
theorem typeABoxDifferential_typeABoxModuleMap_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    (hK' : ∀ n, K ≤ n → Mm'.act n = 0)
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    (hf : ∀ n, K ≤ n → f n = 0)
    (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxModuleMap f φ) +
        N.typeABoxModuleMap f (N.typeABoxDifferential Mm φ) =
      N.typeABoxModuleMap (Mm.morphismDifferential Mm' f) φ := by
  have h := (Mm.matrix X).twistedDifferential_ungradedTwistedMap (Mm'.matrix X)
    (ungradedMatrixFamily X f) N.map_coeff_add_coeff_mul_coeff (Set.mem_univ _) (Set.mem_univ _)
    (K := K) (fun n hn => by
      rw [UngradedAInfinityRightModule.matrix_act, Mm.matrixAct_eq_zero_of_act_eq_zero X (hK n hn),
        zero_apply])
    (fun n hn => by
      rw [UngradedAInfinityRightModule.matrix_act,
        Mm'.matrixAct_eq_zero_of_act_eq_zero X (hK' n hn), zero_apply])
    (fun n hn u _ => by rw [ungradedMatrixFamily_eq_zero_of_eq_zero (hf n hn), zero_apply]) φ
  rw [UngradedAInfinityRightModule.morphismDifferential_ungradedMatrixFamily] at h
  rwa [typeABoxDifferential_def, typeABoxDifferential_def]

/-- **Additivity of the maps induced by bounded families.** -/
theorem typeABoxModuleMap_add_of_eq_zero (N : TypeDStructure d ι X) {K : ℕ}
    {f g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    (hf : ∀ n, K ≤ n → f n = 0) (hg : ∀ n, K ≤ n → g n = 0) :
    N.typeABoxModuleMap (f + g) = N.typeABoxModuleMap f + N.typeABoxModuleMap g := by
  rw [typeABoxModuleMap_def, ungradedMatrixFamily_add, ungradedTwistedMap_add (K := K)
    (fun n hn => by rw [ungradedMatrixFamily_eq_zero_of_eq_zero (hf n hn), zero_apply])
    (fun n hn => by rw [ungradedMatrixFamily_eq_zero_of_eq_zero (hg n hn), zero_apply])]
  rfl

/-- **A homomorphism of bounded modules induces a chain map of box tensor products.** If `∂f = 0`,
then `∂' ∘ (f ⊠ 𝟙) = (f ⊠ 𝟙) ∘ ∂`. -/
theorem typeABoxDifferential_typeABoxModuleMap_of_morphismDifferential_eq_zero_of_act_eq_zero
    [CharP R 2] (N : TypeDStructure d ι X) {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    (hK' : ∀ n, K ≤ n → Mm'.act n = 0)
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    (hf : ∀ n, K ≤ n → f n = 0)
    (hf' : Mm.morphismDifferential Mm' f = 0) (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxModuleMap f φ) =
      N.typeABoxModuleMap f (N.typeABoxDifferential Mm φ) :=
  (add_eq_zero_iff_eq_of_charTwo R).mp <| by
    rw [typeABoxDifferential_typeABoxModuleMap_of_act_eq_zero N hK hK' hf, hf',
      typeABoxModuleMap_zero, LinearMap.zero_apply]

/-- **Homotopic homomorphisms of bounded modules induce homotopic chain maps of box tensor
products.** If `∂h = f + g`, then `f ⊠ 𝟙 + g ⊠ 𝟙 = ∂' ∘ (h ⊠ 𝟙) + (h ⊠ 𝟙) ∘ ∂`. -/
theorem typeABoxModuleMap_add_typeABoxModuleMap_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    (hK' : ∀ n, K ≤ n → Mm'.act n = 0)
    {f g h : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    (hf : ∀ n, K ≤ n → f n = 0) (hg : ∀ n, K ≤ n → g n = 0) (hh : ∀ n, K ≤ n → h n = 0)
    (hfg : Mm.morphismDifferential Mm' h = f + g) (φ : X → M) :
    N.typeABoxModuleMap f φ + N.typeABoxModuleMap g φ =
      N.typeABoxDifferential Mm' (N.typeABoxModuleMap h φ) +
        N.typeABoxModuleMap h (N.typeABoxDifferential Mm φ) := by
  rw [typeABoxDifferential_typeABoxModuleMap_of_act_eq_zero N hK hK' hh, hfg,
    typeABoxModuleMap_add_of_eq_zero N hf hg, LinearMap.add_apply]

/-- **Composites of bounded families induce composite maps.** If `f_{k+1}` and `g_{k+1}` vanish
for `k ≥ K`, then `(g ∘ f) ⊠ 𝟙 = (g ⊠ 𝟙) ∘ (f ⊠ 𝟙)`. -/
theorem typeABoxModuleMap_ungradedFamilyComp_of_eq_zero (N : TypeDStructure d ι X) {K : ℕ}
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    {g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M'')}
    (hf : ∀ n, K ≤ n → f n = 0) (hg : ∀ n, K ≤ n → g n = 0) :
    N.typeABoxModuleMap (ungradedFamilyComp g f) =
      N.typeABoxModuleMap g ∘ₗ N.typeABoxModuleMap f := by
  rw [typeABoxModuleMap_def, ungradedMatrixFamily_ungradedFamilyComp,
    ungradedTwistedMap_ungradedFamilyComp (K := K)
      (fun n hn => by rw [ungradedMatrixFamily_eq_zero_of_eq_zero (hg n hn), zero_apply])
      (fun n hn => by rw [ungradedMatrixFamily_eq_zero_of_eq_zero (hf n hn), zero_apply])]
  rfl

/-- **Homotopy equivalences of bounded modules induce homotopy equivalences of box tensor
products.** If `f : M → M'` and `g : M' → M` are bounded families and `∂h = g ∘ f + 𝟙` for a
bounded family `h`, then `(g ⊠ 𝟙) ∘ (f ⊠ 𝟙) + 𝟙 = ∂ ∘ (h ⊠ 𝟙) + (h ⊠ 𝟙) ∘ ∂` on `M ⊠ N`. -/
theorem typeABoxModuleMap_typeABoxModuleMap_add_of_act_eq_zero [CharP R 2]
    (N : TypeDStructure d ι X) {K : ℕ} (hK : ∀ n, K ≤ n → Mm.act n = 0)
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    {g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M)}
    {h : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M)}
    (hf : ∀ n, K ≤ n → f n = 0) (hg : ∀ n, K ≤ n → g n = 0) (hh : ∀ n, K ≤ n → h n = 0)
    (hgf : Mm.morphismDifferential Mm h = ungradedFamilyComp g f + ungradedFamilyId)
    (φ : X → M) :
    N.typeABoxModuleMap g (N.typeABoxModuleMap f φ) + φ =
      N.typeABoxDifferential Mm (N.typeABoxModuleMap h φ) +
        N.typeABoxModuleMap h (N.typeABoxDifferential Mm φ) := by
  have hgf' : ∀ n, 2 * K + 1 ≤ n → ungradedFamilyComp g f n = 0 := fun n hn =>
    MultilinearMap.ext fun a => LinearMap.ext fun m => by
      rw [ungradedFamilyComp_apply]
      refine sum_eq_zero fun k _ => ?_
      rcases le_or_gt K k with hk | hk
      · simp [hf k hk]
      · simp [hg (n - k) (by omega)]
  have hid : ∀ n, 1 ≤ n → ungradedFamilyId (R := R) (A := A) (M := M) n = 0 := fun n hn => by
    obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ungradedFamilyId_succ n
  rw [← typeABoxModuleMap_add_typeABoxModuleMap_of_act_eq_zero N (K := 2 * K + 1)
      (fun n hn => hK n (by omega)) (fun n hn => hK n (by omega)) hgf'
      (fun n hn => hid n (by omega)) (fun n hn => hh n (by omega)) hgf,
    typeABoxModuleMap_ungradedFamilyComp_of_eq_zero N hf hg, typeABoxModuleMap_ungradedFamilyId,
    LinearMap.comp_apply, LinearMap.id_apply]

/-- The operations of a matrix family along the coefficient matrix of a bounded type `D`
structure, and of its derivative, vanish from the arity bounding its iterates on. -/
private theorem ungradedMatrixFamily_eq_zero_of_isBounded (N : TypeDStructure d ι X) {K : ℕ}
    (hK : ∀ k, K ≤ k → ∀ x z, N.iteratedCoeff k x z = 0)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    ∀ n, K ≤ n → ∀ u : Fin n → Matrix X X A, (∀ l, u l ∈ ({N.coeff, N.coeff.map d} : Set _)) →
      ungradedMatrixFamily X f n u = 0 :=
  fun n hn _ hu => N.ungradedMatrixFamily_eq_zero_of_iteratedCoeff_eq_zero f (hK n hn) hu

/-- **The induced maps with a bounded type `D` structure.** Over a ring of characteristic two, if
the iterates `δᵏ` of `N` vanish for all large `k`, then `∂' ∘ (f ⊠ 𝟙) + (f ⊠ 𝟙) ∘ ∂ = (∂f) ⊠ 𝟙`
for every family `f`, whatever the operations of `M` and `M'`. This holds in particular when the
coefficients of `N` increase a height on its generators (`TauCeti.TypeDStructure.isBounded_of_lt`).
-/
theorem typeABoxDifferential_typeABoxModuleMap_of_isBounded [CharP R 2]
    (N : TypeDStructure d ι X) (hN : N.IsBounded)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxModuleMap f φ) +
        N.typeABoxModuleMap f (N.typeABoxDifferential Mm φ) =
      N.typeABoxModuleMap (Mm.morphismDifferential Mm' f) φ := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  -- In characteristic two `δ * δ = d δ`, and all the families vanish along `δ` and `d δ`.
  have hd := (Mm.matrix X).twistedDifferential_ungradedTwistedMap (Mm'.matrix X)
    (ungradedMatrixFamily X f) N.map_coeff_add_coeff_mul_coeff
    (U := {N.coeff, N.coeff.map d}) (Or.inl rfl) (Or.inr N.map_coeff_eq_coeff_mul_coeff.symm)
    (K := K) (fun n hn => by
      rw [UngradedAInfinityRightModule.matrix_act,
        UngradedAInfinityRightModule.matrixAct_eq_ungradedMatrixFamily]
      exact N.ungradedMatrixFamily_eq_zero_of_isBounded hK Mm.act n hn _ fun _ => Or.inl rfl)
    (fun n hn => by
      rw [UngradedAInfinityRightModule.matrix_act,
        UngradedAInfinityRightModule.matrixAct_eq_ungradedMatrixFamily]
      exact N.ungradedMatrixFamily_eq_zero_of_isBounded hK Mm'.act n hn _ fun _ => Or.inl rfl)
    (N.ungradedMatrixFamily_eq_zero_of_isBounded hK f) φ
  rw [UngradedAInfinityRightModule.morphismDifferential_ungradedMatrixFamily] at hd
  rwa [typeABoxDifferential_def, typeABoxDifferential_def]

/-- **Additivity of the induced maps with a bounded type `D` structure.** -/
theorem typeABoxModuleMap_add_of_isBounded (N : TypeDStructure d ι X) (hN : N.IsBounded)
    (f g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')) :
    N.typeABoxModuleMap (f + g) = N.typeABoxModuleMap f + N.typeABoxModuleMap g := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  rw [typeABoxModuleMap_def, ungradedMatrixFamily_add, ungradedTwistedMap_add
    (fun n hn => N.ungradedMatrixFamily_eq_zero_of_isBounded hK f n hn _ fun _ => Or.inl rfl)
    (fun n hn => N.ungradedMatrixFamily_eq_zero_of_isBounded hK g n hn _ fun _ => Or.inl rfl)]
  rfl

/-- **A homomorphism induces a chain map of box tensor products with a bounded type `D`
structure.** If `∂f = 0`, then `∂' ∘ (f ⊠ 𝟙) = (f ⊠ 𝟙) ∘ ∂`. -/
theorem typeABoxDifferential_typeABoxModuleMap_of_morphismDifferential_eq_zero_of_isBounded
    [CharP R 2] (N : TypeDStructure d ι X) (hN : N.IsBounded)
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    (hf : Mm.morphismDifferential Mm' f = 0) (φ : X → M) :
    N.typeABoxDifferential Mm' (N.typeABoxModuleMap f φ) =
      N.typeABoxModuleMap f (N.typeABoxDifferential Mm φ) :=
  (add_eq_zero_iff_eq_of_charTwo R).mp <| by
    rw [typeABoxDifferential_typeABoxModuleMap_of_isBounded N hN, hf, typeABoxModuleMap_zero,
      LinearMap.zero_apply]

/-- **Homotopic homomorphisms induce homotopic chain maps of box tensor products with a bounded
type `D` structure.** If `∂h = f + g`, then `f ⊠ 𝟙 + g ⊠ 𝟙 = ∂' ∘ (h ⊠ 𝟙) + (h ⊠ 𝟙) ∘ ∂`. -/
theorem typeABoxModuleMap_add_typeABoxModuleMap_of_isBounded [CharP R 2]
    (N : TypeDStructure d ι X) (hN : N.IsBounded)
    {f g h : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    (hfg : Mm.morphismDifferential Mm' h = f + g) (φ : X → M) :
    N.typeABoxModuleMap f φ + N.typeABoxModuleMap g φ =
      N.typeABoxDifferential Mm' (N.typeABoxModuleMap h φ) +
        N.typeABoxModuleMap h (N.typeABoxDifferential Mm φ) := by
  rw [typeABoxDifferential_typeABoxModuleMap_of_isBounded N hN, hfg,
    typeABoxModuleMap_add_of_isBounded N hN, LinearMap.add_apply]

/-- **Composites induce composite maps of box tensor products with a bounded type `D`
structure.** `(g ∘ f) ⊠ 𝟙 = (g ⊠ 𝟙) ∘ (f ⊠ 𝟙)`, whatever the families `f` and `g`. -/
theorem typeABoxModuleMap_ungradedFamilyComp_of_isBounded (N : TypeDStructure d ι X)
    (hN : N.IsBounded)
    (f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M'))
    (g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M'')) :
    N.typeABoxModuleMap (ungradedFamilyComp g f) =
      N.typeABoxModuleMap g ∘ₗ N.typeABoxModuleMap f := by
  obtain ⟨K, hK⟩ := N.isBounded_iff.mp hN
  rw [typeABoxModuleMap_def, ungradedMatrixFamily_ungradedFamilyComp,
    ungradedTwistedMap_ungradedFamilyComp
      (fun n hn => N.ungradedMatrixFamily_eq_zero_of_isBounded hK g n hn _ fun _ => Or.inl rfl)
      (fun n hn => N.ungradedMatrixFamily_eq_zero_of_isBounded hK f n hn _ fun _ => Or.inl rfl)]
  rfl

/-- **Homotopy equivalences of modules induce homotopy equivalences of box tensor products with a
bounded type `D` structure.** If `∂h = g ∘ f + 𝟙` for families `f : M → M'`, `g : M' → M` and
`h : M → M`, then `(g ⊠ 𝟙) ∘ (f ⊠ 𝟙) + 𝟙 = ∂ ∘ (h ⊠ 𝟙) + (h ⊠ 𝟙) ∘ ∂` on `M ⊠ N`. -/
theorem typeABoxModuleMap_typeABoxModuleMap_add_of_isBounded [CharP R 2]
    (N : TypeDStructure d ι X) (hN : N.IsBounded)
    {f : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M')}
    {g : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M' →ₗ[R] M)}
    {h : (n : ℕ) → MultilinearMap (RingHom.id R) (fun _ : Fin n => A) (M →ₗ[R] M)}
    (hgf : Mm.morphismDifferential Mm h = ungradedFamilyComp g f + ungradedFamilyId)
    (φ : X → M) :
    N.typeABoxModuleMap g (N.typeABoxModuleMap f φ) + φ =
      N.typeABoxDifferential Mm (N.typeABoxModuleMap h φ) +
        N.typeABoxModuleMap h (N.typeABoxDifferential Mm φ) := by
  rw [← typeABoxModuleMap_add_typeABoxModuleMap_of_isBounded N hN hgf,
    typeABoxModuleMap_ungradedFamilyComp_of_isBounded N hN, typeABoxModuleMap_ungradedFamilyId,
    LinearMap.comp_apply, LinearMap.id_apply]

end Bounded

/-! ### Morphisms of `A∞` modules -/

section ModuleHom

variable {Mm : UngradedAInfinityRightModule d M} {Mm' : UngradedAInfinityRightModule d M'}

/-- **The map induced by a morphism is the map of its components.** When the operations
`m_{n+1}(·, δ, …, δ)` of the matrix module of the mapping cone of `f` vanish for `n ≥ K`, the map
`T_f` is the map `f ⊠ 𝟙` induced by the family of components of `f`. -/
theorem typeABoxMapOfHom_eq_typeABoxModuleMap (N : TypeDStructure d ι X)
    (f : UngradedAInfinityRightModuleHom Mm Mm') {K : ℕ}
    (hK : ∀ n, K ≤ n → (f.cone.matrixAct X n fun _ => N.coeff) = 0) :
    N.typeABoxMapOfHom f = N.typeABoxModuleMap f.map := by
  -- The matrix family of the components of `f` is a component of the matrix module of the cone.
  have hKf : ∀ n, K ≤ n → (ungradedMatrixFamily X f.map n fun _ => N.coeff) = 0 := fun n hn =>
    LinearMap.ext fun φ => funext fun z => by
      simpa [UngradedAInfinityRightModuleHom.matrixAct_cone_apply, ungradedMatrixFamily_apply,
        ← Pi.zero_def] using congrArg (fun χ => (χ z).2)
          (LinearMap.congr_fun (hK n hn) fun x => ((φ x, 0) : M × M'))
  refine LinearMap.ext fun φ => funext fun z => ?_
  rw [typeABoxMapOfHom_apply_eq_sum _ _ hK, typeABoxModuleMap_apply_eq_sum _ _ hKf]

end ModuleHom

end TypeDStructure

end TauCeti
