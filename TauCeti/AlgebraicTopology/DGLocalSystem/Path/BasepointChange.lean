/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Append
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.Homotopy
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Module
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Module.TensorProduct.Differential

/-!
# Basepoint change of DG local systems

For points `a` and `b` of a space `B`, a DG local system at `a`, that is a right DG module `M`
over the chain algebra `C_*(Ω_a B)`, becomes one at `b` by tensoring with the chain bimodule
`C_*(P_{a→b} B)` of Moore paths from `a` to `b` (`TauCeti.DGLocalSystem.basepointChange`). This
file shows that this ordinary tensor product preserves quasi-isomorphisms
(`TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`). So basepoint change needs no
resolution of the local system: the ordinary tensor product already computes the derived one.

When no Moore path joins `a` to `b`, the path chains vanish and there is nothing to prove.
Otherwise, `C_*(P_{a→b} B)` is a homotopy retract of the free module of rank one as a
**left** module over `C_*(Ω_a B)`. Fix a Moore path `δ` from `a` to `b`. Appending its reversal is
a map `ρ` of left modules from `C_*(P_{a→b} B)` to `C_*(Ω_a B)` (`TauCeti.pathChainToLoopChain`).
Acting on the `0`-chain `[δ]` of `δ` goes back, and the composite `c ↦ ρ(c) · [δ]` is the
push-forward of appending `δ⁻¹` and then `δ` (`TauCeti.pathChainToLoopChain_smul_pathChainPoint`),
which the growing retracing suffix joins to the identity through a homotopy that is graded linear
for the left action (`TauCeti.pathChainAppendHomotopy`). Tensoring with a right module `M` gives
the maps `m ⊗ c ↦ m · ρ(c)` from `M ⊗ C_*(P_{a→b} B)` to `M` and `m ↦ m ⊗ [δ]` back, and the
homotopy `m ⊗ c ↦ (-1) ^ |m| m ⊗ K c` between their composite and the identity. These maps are not
linear over the loops at `b`, but they are natural in `M`, which is all that is needed to transfer
quasi-isomorphisms (`TauCeti.DGRightModuleHom.isQuasiIso_of_homotopyRetract`).

Two successive changes of basepoint, from `a` to `b` and from `b` to `c`, compare with the change
from `a` to `c` through the associator and concatenation of paths
(`TauCeti.DGLocalSystem.basepointChangeComp`), naturally in the local system. When `b` and `c`
are joined by a Moore path `γ`, the comparison is a quasi-isomorphism
(`TauCeti.DGLocalSystem.isQuasiIso_basepointChangeComp_app`): it is a homotopy retract of the
identity of `M ⊗ C_*(P_{a→b} B)`, through the maps above for `γ` on its source and through
appending `γ` and `γ⁻¹` in the second factor on its target.

## Main definitions

* `TauCeti.tensorPathChainAct`, `TauCeti.tensorPathChainPoint`,
  `TauCeti.tensorPathChainHomotopy`: the map `m ⊗ c ↦ m · ρ(c)` from `M ⊗ C_*(P_{a→b} B)` to `M`,
  the map `m ↦ m ⊗ [δ]` back and the homotopy between their composite and the identity, which
  make `M ⊗ C_*(P_{a→b} B)` a homotopy retract of `M`.
* `TauCeti.DGLocalSystem.basepointChange R a b`: basepoint change from `a` to `b`, as a functor.
* `TauCeti.DGLocalSystem.basepointChangeComp R a b c`: the comparison of two successive changes
  of basepoint with the change along the composite.

## Main results

* `TauCeti.tensorPathChainPoint_tensorPathChainAct`: the composite of `m ⊗ c ↦ m · ρ(c)` and
  the map back is homotopic to the identity.
* `TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`: basepoint change preserves
  quasi-isomorphisms.
* `TauCeti.DGLocalSystem.isQuasiIso_basepointChangeComp_app`: the composite of two changes of
  basepoint is quasi-isomorphic to the change along the composite.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
-/

public noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u w v

variable {B : Type u} [TopologicalSpace B] {R : Type w} [CommRing R] {a b c : B}

section BasepointChange

open BalancedTensorProduct DGRightModuleCat

-- Instance search finds a different, but definitionally equal, decomposition of the loop chain
-- algebra than the one recorded in a DG module over it.
local instance (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)) :
    SetLike.GradedSMul
      (InternalGrading.ofDecomposition (cubicalChainGrading (MooreLoopSpace B a) R)).opposite.piece
      M.grading :=
  M.gradedSMul

variable (M : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
  (δ : MoorePathBetween B a b)

/-- The map `M ⊗ C_*(P_{a→b} B) → M`, `m ⊗ c ↦ m · ρ(c)`, where `ρ` appends the reversal of `δ`:
tensoring `ρ` with `M`, followed by the right action. It is the inclusion of the homotopy retract
`M ⊗ C_*(P_{a→b} B)` into `M`, with `tensorPathChainPoint` as the retraction back. -/
def tensorPathChainAct : tensorBimoduleObj M (pathChainBimodule B a b R) →ₗ[R] M :=
  (rid R (loopChainAlgebra B a R) M).toLinearMap ∘ₗ
    map LinearMap.id (pathChainToLoopChain R δ) (fun _ _ ↦ rfl) (pathChainToLoopChain_smul δ)

/-- On pure tensors the map is `m ⊗ c ↦ m · ρ(c)`. -/
@[simp]
theorem tensorPathChainAct_tmul (m : M)
    (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    tensorPathChainAct M δ (tmul R (loopChainAlgebra B a R) m c) =
      op (pathChainToLoopChain R δ c) • m := by
  rw [tensorPathChainAct, LinearMap.comp_apply, map_tmul, LinearEquiv.coe_coe, rid_tmul,
    LinearMap.id_apply]

/-- The map `M → M ⊗ C_*(P_{a→b} B)`, `m ↦ m ⊗ [δ]`, tensoring with the `0`-chain of `δ`. -/
def tensorPathChainPoint : M →ₗ[R] tensorBimoduleObj M (pathChainBimodule B a b R) :=
  (BalancedTensorProduct.mk R (loopChainAlgebra B a R)).flip (pathChainPoint R δ)

/-- The map back is `m ↦ m ⊗ [δ]`. -/
@[simp]
theorem tensorPathChainPoint_apply (m : M) :
    tensorPathChainPoint M δ m = tmul R (loopChainAlgebra B a R) m (pathChainPoint R δ) := by
  rw [tensorPathChainPoint, LinearMap.flip_apply, mk_apply]

variable {M}

/-- The map `m ⊗ c ↦ m · ρ(c)` commutes with the differentials. -/
theorem differential_tensorPathChainAct
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    M.differential (tensorPathChainAct M δ z) =
      tensorPathChainAct M δ
        ((tensorBimoduleObj M (pathChainBimodule B a b R)).differential z) := by
  have h := LinearMap.congr_fun
    (rid_comp_differential (loopChain_isDGAlgebra B a R) M.isDGRightModule)
    (map LinearMap.id (pathChainToLoopChain R δ) (fun _ _ ↦ rfl) (pathChainToLoopChain_smul δ) z)
  have h' := LinearMap.congr_fun (differential_naturality M.isDGRightModule
    (pathChainBimodule B a b R).isDGLeftModule M.isDGRightModule
    (loopChain_isDGAlgebra B a R).isDGLeftModule LinearMap.id (pathChainToLoopChain R δ)
    (fun _ _ ↦ rfl) (pathChainToLoopChain_smul δ) (LinearMap.isHomogeneous_id _) rfl
    (LinearMap.ext fun x ↦ (pathChainToLoopChain_differential δ x).symm)) z
  simp only [LinearMap.comp_apply] at h h'
  rw [tensorPathChainAct, LinearMap.comp_apply, LinearMap.comp_apply, ← h, h']

/-- Tensoring with the `0`-chain of `δ` commutes with the differentials. -/
theorem differential_tensorPathChainPoint (m : M) :
    (tensorBimoduleObj M (pathChainBimodule B a b R)).differential (tensorPathChainPoint M δ m) =
      tensorPathChainPoint M δ (M.differential m) := by
  rw [tensorPathChainPoint_apply, BalancedTensorProduct.differential_tmul,
    cubicalChainModuleDifferential_pathChainPoint, tmul_zero, add_zero, tensorPathChainPoint_apply]

/-- The map `m ⊗ c ↦ m · ρ(c)` is natural in `M`. -/
theorem tensorPathChainAct_tensorBimoduleMap
    {N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} (f : M ⟶ N)
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    tensorPathChainAct N δ (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R)) z) =
      f (tensorPathChainAct M δ z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' => simp only [map_add, hz, hz']
  | ht m c =>
    rw [tensorBimoduleMap_tmul, tensorPathChainAct_tmul, tensorPathChainAct_tmul,
      DGBimoduleCat.id_apply]
    exact (map_smul f _ m).symm

/-- Tensoring with the `0`-chain of `δ` is natural in `M`. -/
theorem tensorBimoduleMap_tensorPathChainPoint
    {N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} (f : M ⟶ N) (m : M) :
    tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R)) (tensorPathChainPoint M δ m) =
      tensorPathChainPoint N δ (f m) := by
  rw [tensorPathChainPoint_apply, tensorPathChainPoint_apply, tensorBimoduleMap_tmul,
    DGBimoduleCat.id_apply]

variable (M) in
/-- The chain homotopy `m ⊗ c ↦ (-1) ^ |m| m ⊗ K c` on `M ⊗ C_*(P_{a→c} B)`, for a Moore path `γ`
from `b` to `c` and the homotopy `K = pathChainAppendHomotopy R γ a` growing the retracing
suffix. -/
def tensorPathChainHomotopy (γ : MoorePathBetween B b c) :
    tensorBimoduleObj M (pathChainBimodule B a c R) →ₗ[R]
      tensorBimoduleObj M (pathChainBimodule B a c R) :=
  koszulMapRight M.grading (fun hα x ↦ pathChainAppendHomotopy_smul γ a hα x)

/-- On pure tensors, the first factor acquires its Koszul twist. -/
@[simp]
theorem tensorPathChainHomotopy_tmul (γ : MoorePathBetween B b c) (m : M)
    (x : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    tensorPathChainHomotopy M γ (tmul R (loopChainAlgebra B a R) m x) =
      tmul R (loopChainAlgebra B a R) ((InternalGrading.ofDecomposition M.grading).koszulTwist 1 m)
        (pathChainAppendHomotopy R γ a x) :=
  koszulMapRight_tmul _ m x

/-- On a homogeneous first factor of degree `q`, the homotopy carries the sign `(-1) ^ q`. -/
theorem tensorPathChainHomotopy_tmul_of_mem (γ : MoorePathBetween B b c) {q : ℤ} {m : M}
    (hm : m ∈ M.grading q)
    (x : cubicalChainModule (MoorePathBetween B a c) (MooreLoopSpace B c) R) :
    tensorPathChainHomotopy M γ (tmul R (loopChainAlgebra B a R) m x) =
      ((q.negOnePow : ℤ) : R) •
        tmul R (loopChainAlgebra B a R) m (pathChainAppendHomotopy R γ a x) :=
  koszulMapRight_tmul_of_mem _ hm x

/-- **`M ⊗ C_*(P_{a→b} B)` is a homotopy retract of `M`**: following `m ⊗ c ↦ m · ρ(c)` by
`m ↦ m ⊗ [δ]` is homotopic to the identity, through `tensorPathChainHomotopy M δ`. -/
theorem tensorPathChainPoint_tensorPathChainAct
    (z : tensorBimoduleObj M (pathChainBimodule B a b R)) :
    tensorPathChainPoint M δ (tensorPathChainAct M δ z) =
      z + (tensorBimoduleObj M (pathChainBimodule B a b R)).differential
          (tensorPathChainHomotopy M δ z) +
        tensorPathChainHomotopy M δ
          ((tensorBimoduleObj M (pathChainBimodule B a b R)).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' =>
    simp only [map_add, hz, hz']
    abel
  | ht m c =>
    have h := tmul_sub_tmul_eq_add_koszulMapRight (ℳ := M.grading)
      (N := (pathChainBimodule B a b R).carrier) (N' := (pathChainBimodule B a b R).carrier)
      (dN := (pathChainBimodule B a b R).differential)
      (dN' := (pathChainBimodule B a b R).differential)
      (D := (tensorBimoduleObj M (pathChainBimodule B a b R)).differential)
      (D' := (tensorBimoduleObj M (pathChainBimodule B a b R)).differential)
      M.isDGRightModule.isHomogeneous
      (fun hα x ↦ pathChainAppendHomotopy_smul δ a hα x)
      (g₁ := cubicalChainModuleLinearMap R
        ((MoorePathBetween.append δ a).comp (MoorePathBetween.append δ.symm a)))
      (g₂ := LinearMap.id) (fun x ↦ (pathChainAppendHomotopy_spec δ a x).symm)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x) m c
    rw [LinearMap.id_apply, sub_eq_iff_eq_add'] at h
    rw [tensorPathChainAct_tmul, tensorPathChainPoint_apply, balance,
      pathChainToLoopChain_smul_pathChainPoint, h, add_assoc, tensorPathChainHomotopy]

/-- **Changing the basepoint preserves quasi-isomorphisms.** For every quasi-isomorphism
`f : M → N` of DG local systems at `a`, the tensored morphism
`f ⊗ 1 : M ⊗ C_*(P_{a→b} B) → N ⊗ C_*(P_{a→b} B)` of DG local systems at `b` is a
quasi-isomorphism. So the ordinary tensor product with the path bimodule already computes the
derived one. -/
theorem isQuasiIso_tensorBimoduleMap_pathChainBimodule
    {M N : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R)} {f : M ⟶ N}
    (hf : IsQuasiIso f) : IsQuasiIso (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))) := by
  -- Instance search does not see the structures of a tensor product through its carrier.
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).moduleOp
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).scalarTower
  let := (tensorBimoduleObj M (pathChainBimodule B a b R)).gradedSMul
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).moduleOp
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).scalarTower
  let := (tensorBimoduleObj N (pathChainBimodule B a b R)).gradedSMul
  rcases isEmpty_or_nonempty (MoorePathBetween B a b) with hB | hB
  · -- Without Moore paths from `a` to `b`, there are no path chains, so both tensor products
    -- vanish.
    have hc (c : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) : c = 0 := by
      induction c using cubicalChainModule.induction_on with
      | add c c' ih ih' => rw [ih, ih', add_zero]
      | lof q c =>
        induction c using NormalizedCubicalChain.induction_on with
        | zero => exact map_zero _
        | add c c' ih ih' => rw [map_add, ih, ih', add_zero]
        | smul r c ih => rw [map_smul, ih, smul_zero]
        | ofCube c => exact isEmptyElim (c 0)
    have hz (L : DGRightModuleCat.{w, max u w, v} (loopChain_isDGAlgebra B a R))
        (z : tensorBimoduleObj L (pathChainBimodule B a b R)) : z = 0 := by
      induction z using BalancedTensorProduct.induction_on with
      | ht m c => rw [hc c, tmul_zero]
      | ha z z' ih ih' => rw [ih, ih', add_zero]
    rw [IsQuasiIso, DGRightModuleHom.isQuasiIso_iff_forall_exists]
    exact fun x y _ _ ↦ ⟨0, 0, by rw [map_zero, hz M x],
      by rw [map_zero, map_zero, add_zero, hz N y]⟩
  · obtain ⟨δ⟩ := hB
    exact DGRightModuleHom.isQuasiIso_of_homotopyRetract
      (tensorBimoduleMap f (𝟙 (pathChainBimodule B a b R))) (f.toLinearMap.restrictScalars R)
      ((DGRightModuleHom.isQuasiIso_iff_forall_exists f).1 hf)
      (tensorPathChainAct M δ) (tensorPathChainPoint M δ) (tensorPathChainHomotopy M δ)
      (tensorPathChainAct N δ) (tensorPathChainPoint N δ) (tensorPathChainHomotopy N δ)
      (differential_tensorPathChainAct δ) (differential_tensorPathChainPoint δ)
      (differential_tensorPathChainAct δ) (differential_tensorPathChainPoint δ)
      (tensorPathChainPoint_tensorPathChainAct δ) (tensorPathChainPoint_tensorPathChainAct δ)
      (tensorPathChainAct_tensorBimoduleMap δ f) (tensorBimoduleMap_tensorPathChainPoint δ f)

namespace DGLocalSystem

variable (R) in
/-- **Basepoint change** of DG local systems from `b` to `c`: the ordinary tensor product
`𝓕 ↦ 𝓕 ⊗_{C_*(Ω_b B)} C_*(P_{b→c} B)` with the chains on the Moore paths from `b` to `c`, a DG
local system at `c` through the loops at `c` acting on the end of the paths. It preserves
quasi-isomorphisms (`TauCeti.isQuasiIso_tensorBimoduleMap_pathChainBimodule`). -/
abbrev basepointChange (b c : B) :
    DGLocalSystem.{v} B b R ⥤ DGLocalSystem.{max v u w} B c R where
  obj 𝓕 := tensorBimoduleObj 𝓕 (pathChainBimodule B b c R)
  map f := tensorBimoduleMap f (𝟙 _)
  map_id _ := tensorBimoduleMap_id _ _
  map_comp f g := by
    rw [← tensorBimoduleMap_comp, Category.comp_id]

/-- Basepoint change acts on morphisms in the first tensor factor. -/
@[simp]
theorem basepointChange_map_tmul {𝓕 𝓖 : DGLocalSystem.{v} B b R} (f : 𝓕 ⟶ 𝓖) (x : 𝓕)
    (σ : cubicalChainModule (MoorePathBetween B b c) (MooreLoopSpace B c) R) :
    (basepointChange R b c).map f (tmul R (loopChainAlgebra B b R) x σ) =
      tmul R (loopChainAlgebra B b R) (f x) σ :=
  (tensorBimoduleMap_tmul f (𝟙 (pathChainBimodule B b c R)) x σ).trans
    (by rw [DGBimoduleCat.id_apply])

section Comp

variable (𝓕 : DGLocalSystem.{v} B a R)

/-- Appending a path `γ` from `b` to `c` in the second factor, `x ⊗ σ ↦ x ⊗ (σ ⋆ γ)`. -/
def basepointChangeAppend (γ : MoorePathBetween B b c) :
    (basepointChange R a b).obj 𝓕 →ₗ[R] (basepointChange R a c).obj 𝓕 :=
  BalancedTensorProduct.map LinearMap.id (pathChainAppend R γ a) (fun _ _ ↦ rfl)
    (pathChainAppend_smul γ a)

/-- On pure tensors, appending acts on the second factor. -/
@[simp]
theorem basepointChangeAppend_tmul (γ : MoorePathBetween B b c) (x : 𝓕)
    (σ : cubicalChainModule (MoorePathBetween B a b) (MooreLoopSpace B b) R) :
    basepointChangeAppend 𝓕 γ (tmul R (loopChainAlgebra B a R) x σ) =
      tmul R (loopChainAlgebra B a R) x (pathChainAppend R γ a σ) := by
  rw [basepointChangeAppend, BalancedTensorProduct.map_tmul, LinearMap.id_apply]

/-- Appending in the second factor is a chain map. -/
theorem differential_basepointChangeAppend (γ : MoorePathBetween B b c)
    (z : (basepointChange R a b).obj 𝓕) :
    ((basepointChange R a c).obj 𝓕).differential (basepointChangeAppend 𝓕 γ z) =
      basepointChangeAppend 𝓕 γ (((basepointChange R a b).obj 𝓕).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht x σ =>
    induction x using DirectSum.Decomposition.inductionOn 𝓕.grading with
    | zero => simp
    | @homogeneous p x =>
      rw [basepointChangeAppend_tmul, tensorBimoduleObj_differential_tmul x.2,
        tensorBimoduleObj_differential_tmul x.2, map_add, map_zsmul_unit,
        basepointChangeAppend_tmul, basepointChangeAppend_tmul]
      -- The differentials of the bundled path bimodules are the cubical boundaries by definition.
      erw [cubicalChainModuleDifferential_pathChainAppend]
    | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | ha z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

/-- **Appending `γ⁻¹` and then `γ` in the second factor is homotopic to the identity**, through
`tensorPathChainHomotopy 𝓕 γ`. -/
theorem basepointChangeAppend_basepointChangeAppend_symm (γ : MoorePathBetween B b c)
    (z : (basepointChange R a c).obj 𝓕) :
    basepointChangeAppend 𝓕 γ (basepointChangeAppend 𝓕 γ.symm z) =
      z + ((basepointChange R a c).obj 𝓕).differential (tensorPathChainHomotopy 𝓕 γ z) +
        tensorPathChainHomotopy 𝓕 γ (((basepointChange R a c).obj 𝓕).differential z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ha z z' hz hz' =>
    simp only [map_add, hz, hz']
    abel
  | ht m σ =>
    have h := tmul_sub_tmul_eq_add_koszulMapRight (ℳ := 𝓕.grading)
      (N := (pathChainBimodule B a c R).carrier) (N' := (pathChainBimodule B a c R).carrier)
      (dN := (pathChainBimodule B a c R).differential)
      (dN' := (pathChainBimodule B a c R).differential)
      (D := (tensorBimoduleObj 𝓕 (pathChainBimodule B a c R)).differential)
      (D' := (tensorBimoduleObj 𝓕 (pathChainBimodule B a c R)).differential)
      𝓕.isDGRightModule.isHomogeneous
      (fun hα x ↦ pathChainAppendHomotopy_smul γ a hα x)
      (g₁ := cubicalChainModuleLinearMap R
        ((MoorePathBetween.append γ a).comp (MoorePathBetween.append γ.symm a)))
      (g₂ := LinearMap.id) (fun x ↦ (pathChainAppendHomotopy_spec γ a x).symm)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x)
      (fun hm x ↦ tensorBimoduleObj_differential_tmul hm x) m σ
    rw [LinearMap.id_apply, sub_eq_iff_eq_add'] at h
    rw [basepointChangeAppend_tmul, basepointChangeAppend_tmul,
      pathChainAppend_pathChainAppend_symm, h, add_assoc, tensorPathChainHomotopy]

variable (R) in
/-- The composite of two basepoint changes compared with the change along the composite: the
associator followed by concatenation of paths,
`(𝓕 ⊗ C_*(P_{a→b})) ⊗ C_*(P_{b→c}) → 𝓕 ⊗ C_*(P_{a→c})`. -/
def basepointChangeComp (a b c : B) :
    (basepointChange R a b ⋙ basepointChange R b c : DGLocalSystem.{v} B a R ⥤ _) ⟶
      basepointChange R a c where
  app 𝓕 := ((DGBimoduleCat.tensorAssoc 𝓕.toScalarBimodule (pathChainBimodule B a b R)
      (pathChainBimodule B b c R)).hom ≫
    DGBimoduleCat.tensorMap (𝟙 _) (pathChainConcat B a b c R)).val
  naturality 𝓕 𝓖 f := by
    apply tensorBimoduleObj_hom_ext
    intro z τ
    induction z using BalancedTensorProduct.induction_on with
    | ht x σ =>
      rw [DGRightModuleCat.comp_apply, DGRightModuleCat.comp_apply, Functor.comp_map,
        basepointChange_map_tmul, basepointChange_map_tmul]
      -- The components are underlying maps of bimodule morphisms; apply them as such.
      erw [DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply]
      rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorAssoc_hom_tmul,
        DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply,
        DGBimoduleCat.id_apply, basepointChange_map_tmul]
    | ha z w hz hw => simp only [add_tmul, map_add, hz, hw]

/-- The component of the comparison at `𝓕` is the associator followed by concatenation of
paths, as a morphism of DG bimodules. -/
theorem basepointChangeComp_app :
    (basepointChangeComp R a b c).app 𝓕 =
      ((DGBimoduleCat.tensorAssoc 𝓕.toScalarBimodule (pathChainBimodule B a b R)
          (pathChainBimodule B b c R)).hom ≫
        DGBimoduleCat.tensorMap (𝟙 _) (pathChainConcat B a b c R)).val :=
  (rfl)

/-- **The composite of two basepoint changes is the change along the composite**: the comparison
`(𝓕 ⊗ C_*(P_{a→b})) ⊗ C_*(P_{b→c}) → 𝓕 ⊗ C_*(P_{a→c})` is a quasi-isomorphism when `b` and
`c` are joined by a Moore path `γ`. It is a homotopy retract of the identity of
`𝓕 ⊗ C_*(P_{a→b})`: through `x ↦ x ⊗ [γ]` and `x ⊗ τ ↦ x · ρ(τ)` on the source, and appending
`γ` and `γ⁻¹` in the second factor on the target. -/
theorem isQuasiIso_basepointChangeComp_app (γ : MoorePathBetween B b c) :
    IsQuasiIso ((basepointChangeComp R a b c).app 𝓕) := by
  -- Instance search does not see the structures of a tensor product through its carrier.
  let := ((basepointChange R b c).obj ((basepointChange R a b).obj 𝓕)).moduleOp
  let := ((basepointChange R b c).obj ((basepointChange R a b).obj 𝓕)).scalarTower
  let := ((basepointChange R a c).obj 𝓕).moduleOp
  let := ((basepointChange R b c).obj ((basepointChange R a b).obj 𝓕)).gradedSMul
  let := ((basepointChange R a c).obj 𝓕).scalarTower
  let := ((basepointChange R a c).obj 𝓕).gradedSMul
  refine DGRightModuleHom.isQuasiIso_of_homotopyRetract _ LinearMap.id
    (fun _ y _ hxy ↦ ⟨y, 0, hxy.symm, by rw [map_zero, add_zero, LinearMap.id_apply]⟩)
    (tensorPathChainAct _ γ) (tensorPathChainPoint _ γ) (tensorPathChainHomotopy _ γ)
    (basepointChangeAppend 𝓕 γ.symm) (basepointChangeAppend 𝓕 γ) (tensorPathChainHomotopy 𝓕 γ)
    (differential_tensorPathChainAct γ) (differential_tensorPathChainPoint γ)
    (differential_basepointChangeAppend 𝓕 γ.symm) (differential_basepointChangeAppend 𝓕 γ)
    (tensorPathChainPoint_tensorPathChainAct γ)
    (basepointChangeAppend_basepointChangeAppend_symm 𝓕 γ) (fun z ↦ ?_) (fun y ↦ ?_)
  · rw [LinearMap.id_apply]
    induction z using BalancedTensorProduct.induction_on with
    | ht y τ =>
      induction y using BalancedTensorProduct.induction_on with
      | ht x σ =>
        rw [tensorPathChainAct_tmul, basepointChangeComp_app]
        -- The component is the underlying map of a bimodule morphism, and the right action on
        -- the tensor product is the balanced one; apply them as such.
        erw [DGBimoduleCat.comp_apply, smul_tmul_right]
        rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorMap_tmul,
          DGBimoduleCat.id_apply, basepointChangeAppend_tmul, op_pathChainToLoopChain_smul]
      | ha y w hy hw => rw [add_tmul, map_add, map_add, hy, hw, map_add]
    | ha z w hz hw => rw [map_add, map_add, hz, hw, map_add]
  · induction y using BalancedTensorProduct.induction_on with
    | ht x σ =>
      rw [tensorPathChainPoint_apply, basepointChangeComp_app]
      -- The component is the underlying map of a bimodule morphism; apply it as such.
      erw [DGBimoduleCat.comp_apply]
      rw [DGBimoduleCat.tensorAssoc_hom_tmul, DGBimoduleCat.tensorMap_tmul, DGBimoduleCat.id_apply,
        pathChainConcat_tmul_pathChainPoint, LinearMap.id_apply, basepointChangeAppend_tmul]
    | ha y w hy hw => rw [map_add, map_add, hy, hw, map_add, map_add]

end Comp

end DGLocalSystem

end BasepointChange

end TauCeti
