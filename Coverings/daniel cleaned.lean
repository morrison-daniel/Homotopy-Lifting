import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Covering
import Mathlib.Topology.LocalHomeomorph
import Mathlib.Topology.UnitInterval
import Coverings.lean3

open Topology Filter unitInterval Bundle Function Set
namespace IsCoveringMap

/-
Notation:
`E` : the covering space of `X`
`F` : the lift of the map `f`
`F₀` : the start of `F`, i.e. `F₀ = F(y, 0)`

`U : ι → Set α` : collection of (open) sets of α
`s ⊆ ⋃ i, U i` : a (possibly infinite) open cover 
`∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i` : existence of finite subcover

`Continuous f` : `f` is globally continuous
`ContinuousAt f a` : `f` is continuous at the point a

`IsCompact (s : Set α)` : the set s is compact in topological space `α`

`Trivialization F proj` : local trivialization of `proj : E → B` with fiber `F`
`IsEvenlyCovered x ι` : `DiscreteTopology ι ∧ ∃ t : Trivialization ι p, x ∈ t.baseSet`
                      : fiber over x has discrete topology & has a local trivialization
`IsCoveringMap (f : E → X)` : `∀ x, IsEvenlyCovered (f x) (f ⁻¹' {x})`

`∀ᶠ y ∈ 𝓝 x, P y` : exists a nbhd `U` of `x` such that `y ∈ U → P y`

Theorems:
`toTrivialization` : gets local trivialization above a point from a covering map
`IsCompact.elim_finite_subcover` : reduces open cover to finite cover

`isCompact_singleton` : set of a single point is compact
`isCompact_prod` : product of compact sets is compact
-/

variable {X E : Type _} [TopologicalSpace X] [TopologicalSpace E]
variable {p : C(E, X)} {hp : IsCoveringMap p}

structure LiftSetup (p : C(E, X)) (Y : Type _) [TopologicalSpace Y] where
  f : C(Y × I, X)
  F₀ : C(Y, E)
  f_eq_pF₀ : ∀ y : Y, f (y, 0) = p (F₀ y)

variable {Y : Type _} [TopologicalSpace Y]
variable (φ : LiftSetup p Y)

lemma trivial_nbhd (y : Y) (t : I) :
  ∃ triv : Trivialization (p ⁻¹' {φ.f (y, t)}) p, φ.f ⁻¹' triv.baseSet ∈ 𝓝 (y, t) := by
    specialize hp <| φ.f (y, t)
    let triv : Trivialization (p ⁻¹' {φ.f (y, t)}) p := by
      apply IsEvenlyCovered.toTrivialization hp
    use triv 
    rw [mem_nhds_iff]
    use φ.f ⁻¹' triv.baseSet
    constructor
    . rfl
    . constructor
      . exact IsOpen.preimage φ.f.continuous_toFun triv.open_baseSet
      . rw [preimage]
        exact IsEvenlyCovered.mem_toTrivialization_baseSet hp

#check nhds_prod_eq

lemma trivial_tube (y : Y) : 
  ∃ U ∈ 𝓝 (y), ∀ t : I, ∃ V ∈ 𝓝 (t), ∃ triv : Trivialization (p ⁻¹' {φ.f (y, t)}) p, U ×ˢ V ⊆ φ.f ⁻¹' triv.baseSet := by
    sorry

theorem existence_of_homotopy_lift : ∃ F : C(Y × I, E), p ∘ F = f ∧ (fun y ↦ F (y, 0)) = F₀ := by
  sorry